import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_x_pyy_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq19 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq21 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : (M.op x y) = (M.op x y) := by grind
  have eq25 : (M.op x y) = (M.op x y) := by grind
  clear eq24
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq27 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq26
  have eq28 : (σ x) = (σ x) := by grind
  have eq29 : (σ x) = (σ x) := by grind
  clear eq28
  have eq30 : (σ y) = (σ y) := by grind
  have eq31 : (σ y) = (σ y) := by grind
  clear eq30
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq33 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq32
  have eq34 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq19
    | (have j1 := eq20 X0
       grind)
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq36 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq23 eq22
    | (have j1 := eq23 X0
       grind)
    | exact resolve eq22 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq44 : (M.op x y) = (M.op x (τ (σ y))) := by
    first
    | (have i₁ := eq25
       have i₂ := eq41
       grind)
    | exact superpose eq41 eq25
    | exact resolve eq25 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq41
  have eq45 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq44
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq44
    | exact resolve eq44 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq44
  have eq48 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (τ X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq48
    | exact resolve eq48 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (M.op x y) X0
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 X0 (M.op x y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq68 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq55 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq55
    | exact resolve eq55 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq88 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq60
    | exact resolve eq60 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq105 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (k X1 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 (M.op X2 X2)) X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq14
    | (have j0 := eq14 (M.op (M.op (M.op X1 (M.op X2 X2)) X0) (M.op (M.op X1 (M.op X2 X2)) X0)) X0
       grind)
    | exact resolve eq14 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq45 eq14
    | (have j0 := eq14 (M.op x y) (k (τ (σ y)) (τ (σ x)))
       grind)
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))) ∨ (M.op (k X0 (M.op X1 (M.op X2 X2))) X1) = X0 ∨ (M.op X1 (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 (M.op X2 X2))
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq51
    | exact resolve eq51 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq164 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq50 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X1
       have i₂ := eq50 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq50 eq9
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq50 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       grind)
    | exact superpose eq50 eq9
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq50 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq50 eq9
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq108 eq34
    | exact resolve eq34 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq261 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op (M.op X1 (M.op X2 X2)) X0) X3 X4 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq49
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq49 (M.op X1 X0) X4 X5 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1)
       have i₂ := eq49 X1 X2 X3 X0
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (τ (σ y)) = (M.op (M.op x y) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (τ (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq45 eq49
    | exact resolve eq49 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq33 eq49
    | (have j0 := eq49 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq49 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 x (M.op X0 X0) X2
       have i₂ := eq50 x (M.op X0 X0) X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = (M.op X0 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) X0))) ∨ (k X1 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op (M.op X1 (M.op X2 X2)) X0) X3 X4 (M.op (M.op X1 (M.op X2 X2)) X0)
       have i₂ := eq105 X0 X1 X2
       grind)
    | exact superpose eq105 eq49
    | (have j1 := eq105 X0 X1 X2
       grind)
    | exact resolve eq49 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq575 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = X1 ∨ (k X1 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq574 X0 X1 X2 x x
       have i₂ := eq261 X0 X1 X2 x x
       grind)
    | exact superpose eq261 eq574
    | (have j0 := eq574 X0 X1 X2 x x
       grind)
    | exact resolve eq574 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq576 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq575 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq580 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq106 eq15
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq581 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq580
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq580
    | exact resolve eq580 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq582 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq581
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq581
    | exact resolve eq581 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq583 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq27 eq582
    | exact resolve eq582 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq599 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (M.op x y) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq583 eq49
    | exact resolve eq49 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq600 : (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq264 eq599
    | exact resolve eq599 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq599
  have eq601 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq600
  have eq662 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op X0 (M.op X1 X1)) X2) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op X0 (M.op X1 X1)))) ∨ (M.op (k X2 (M.op X0 (M.op X1 X1))) X0) = X2 ∨ (M.op X0 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X0 (M.op X1 X1)) X3 X4 (M.op X0 (M.op X1 X1))
       have i₂ := eq111 X2 X0 X1
       grind)
    | (have i₁ := eq49 (M.op X1 (M.op X2 X2)) X1 X2 X0
       have i₂ := eq111 X0 X1 X2
       grind)
    | exact superpose eq111 eq49
    | (have j1 := eq111 X2 X0 X1
       grind)
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq666 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = X2 ∨ (M.op (k X2 (M.op X0 (M.op X1 X1))) X0) = X2 ∨ (M.op X0 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq662 X0 X1 X2 x x
       have i₂ := eq49 (M.op X0 (M.op X1 X1)) x x X2
       grind)
    | exact superpose eq49 eq662
    | (have j0 := eq662 X0 X1 X2 x x
       grind)
    | exact resolve eq662 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq667 : ∀ X0 X1 X2 : G, (M.op (k X2 (M.op X0 (M.op X1 X1))) X0) = X2 ∨ (M.op X0 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq666 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq685 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq601 eq224
    | (have r₁ := eq224
       have r₂ := eq601
       grind)
    | exact resolve eq224 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq601
  have eq686 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq685
  have eq838 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq686 eq49
    | exact resolve eq49 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq841 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq266 eq838
    | exact resolve eq838 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq838
  have eq842 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq841
  have eq844 : (σ y) = (σ (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq842 eq36
    | exact resolve eq36 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq845 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq844
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq844
    | exact resolve eq844 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq846 : (σ x) = (σ y) := by grind
  clear eq845
  have eq999 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq846 eq45
    | exact resolve eq45 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1000 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq846 eq33
    | exact resolve eq33 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq846
  have eq1006 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op (σ x) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1000 eq50
    | exact resolve eq50 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1000 eq50
    | exact resolve eq50 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1015 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1000 eq168
    | exact resolve eq168 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1031 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1007 X0 x
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq1007
    | exact resolve eq1007 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1072 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (σ x) (σ y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1000 eq169
    | exact resolve eq169 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1097 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq169 X0 X1 x
       grind)
    | exact superpose eq169 eq9
    | exact resolve eq9 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : ∀ X0 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op (σ x) (σ y)))) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq1097 X0 x X3
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq1097
    | exact resolve eq1097 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1133 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1072 X0 x
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq1072
    | exact resolve eq1072 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1179 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq999 eq169
    | exact resolve eq169 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1194 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1179 X0 x
       have i₂ := eq1015 (M.op X0 sF2) x
       grind)
    | exact superpose eq1015 eq1179
    | exact resolve eq1179 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1209 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1031 eq50
    | exact resolve eq50 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1214 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1031 eq169
    | exact resolve eq169 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1219 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1214 x
       have i₂ := eq1015 sF6 x
       grind)
    | exact superpose eq1015 eq1214
    | exact resolve eq1214 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1237 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq999 eq170
    | exact resolve eq170 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1333 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1237 X0 x
       have i₂ := eq1015 (M.op sF2 X0) x
       grind)
    | exact superpose eq1015 eq1237
    | exact resolve eq1237 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1393 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1133 eq49
    | exact resolve eq49 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1396 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (M.op X1 X1) (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1393 X0 X1 x
       have i₂ := eq1015 (M.op X1 X1) x
       grind)
    | exact superpose eq1015 eq1393
    | exact resolve eq1393 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1402 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1209 eq1396
    | exact resolve eq1396 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1405 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq1031 eq1402
    | exact resolve eq1402 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1407 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X3 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq271 X3 X2 X2
       have i₂ := eq164 X1 X0 X2
       grind)
    | (have i₁ := eq271 X0 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq164 X0 X1 X2
       grind)
    | exact superpose eq164 eq271
    | exact resolve eq271 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq1457 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq271 X0 (M.op (M.op X1 X1) X0) X2
       have i₂ := eq271 X1 X0 X0
       grind)
    | exact superpose eq271 eq271
    | exact resolve eq271 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1531 : ∀ X0 X2 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X2) X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1457 X0 x X2
       have i₂ := eq1405 x
       grind)
    | exact superpose eq1405 eq1457
    | exact resolve eq1457 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq1554 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1407 X0 X1 X2 x
       have i₂ := eq1405 x
       grind)
    | exact superpose eq1405 eq1407
    | exact resolve eq1407 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1576 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X2)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1554 X0 x X2
       have i₂ := eq1015 (M.op X0 X0) x
       grind)
    | exact superpose eq1015 eq1554
    | exact resolve eq1554 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq1591 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X2)) = X2 := by
    intro X2
    first
    | exact superpose eq1209 eq1576
    | exact resolve eq1576 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576
  have eq1672 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X1)) X0 X1
       have i₂ := eq1405 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq1405 eq9
    | exact resolve eq9 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1674 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq999
       have i₂ := eq1405 (τ sF4)
       grind)
    | exact superpose eq1405 eq999
    | exact resolve eq999 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1681 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq1674 eq1672
    | exact resolve eq1672 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1716 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq1681 X0 x
       have i₂ := eq1405 x
       grind)
    | exact superpose eq1405 eq1681
    | exact resolve eq1681 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681
  have eq1726 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1674 eq1716
    | exact resolve eq1716 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716
  have eq1749 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq1674 eq1133
    | exact resolve eq1133 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1751 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq1674 eq1031
    | exact resolve eq1031 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1753 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1674 eq34
    | exact resolve eq34 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1941 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq1674 eq1591
    | exact resolve eq1591 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591
  have eq2667 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1194 eq49
    | exact resolve eq49 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1194
  have eq2670 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (M.op X1 X1) (M.op (σ x) (σ y))) (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2667 X0 X1 x
       have i₂ := eq1015 (M.op X1 X1) x
       grind)
    | exact superpose eq1015 eq2667
    | exact resolve eq2667 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq2684 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1209 eq2670
    | exact resolve eq2670 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670
  have eq2693 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op x y) (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1674 eq2684
    | exact resolve eq2684 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684
  have eq2700 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq1751 eq2693
    | exact resolve eq2693 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2693
  have eq4915 : ∀ X0 X1 X2 : G, (M.op (k X1 X0) (M.op (M.op X2 X2) X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq667 (M.op (M.op X0 X0) X2) X1 X2
       have i₂ := eq170 X0 X1 X2
       grind)
    | exact superpose eq170 eq667
    | exact resolve eq667 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq4947 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op X1 X1))) ∨ (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1133 (k x (M.op sF6 (M.op X1 X1)))
       have i₂ := eq667 sF6 X1 x
       grind)
    | exact superpose eq667 eq1133
    | (have j1 := eq667 (M.op (σ x) (σ y)) X1 X0
       grind)
    | exact resolve eq1133 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq1133
  have eq4951 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4947 X0 X1
       have i₂ := eq1015 sF6 X1
       grind)
    | exact superpose eq1015 eq4947
    | (have j0 := eq4947 X0 X1
       grind)
    | exact resolve eq4947 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4947
  have eq4980 : ∀ X0 X1 : G, (M.op (k X1 X0) (M.op (M.op (σ x) (σ y)) X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4915 X0 X1 x
       have i₂ := eq1405 x
       grind)
    | exact superpose eq1405 eq4915
    | (have j0 := eq4915 (M.op (k X1 X0) (M.op (M.op (σ x) (σ y)) X0)) X1 x
       grind)
    | exact resolve eq4915 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915
  have eq5004 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1219 eq4951
    | (have j0 := eq4951 X0 X1
       grind)
    | exact resolve eq4951 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951
  have eq5033 : ∀ X0 X1 : G, (M.op (k X1 X0) (M.op (M.op x y) X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq1674 eq4980
    | (have j0 := eq4980 (M.op (k X1 X0) (M.op (M.op x y) X0)) X1
       grind)
    | exact resolve eq4980 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4980
  have eq5057 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1674 eq5004
    | (have j0 := eq5004 X0 X1
       grind)
    | exact resolve eq5004 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5004
  have eq5100 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = X0 ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq5057 X0 x
       have i₂ := eq1015 sF6 x
       grind)
    | exact superpose eq1015 eq5057
    | (have j0 := eq5057 X0 x
       grind)
    | exact resolve eq5057 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5057
  have eq5139 : ∀ X0 : G, (M.op (σ x) (σ y)) = X0 ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1219 eq5100
    | (have j0 := eq5100 X0
       grind)
    | exact resolve eq5100 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq5100
  have eq5178 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq1674 eq5139
    | (have j0 := eq5139 X0
       grind)
    | exact resolve eq5139 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5139
  have eq5592 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X4)) = (M.op X1 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq261 X1 (M.op X0 (M.op X4 X4)) x X2 X3
       have i₂ := eq169 X0 X4 x
       grind)
    | exact superpose eq169 eq261
    | exact resolve eq261 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq5680 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 (M.op X4 X4)) X1)) = (M.op X0 (M.op (M.op X5 X5) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq271 X5 X1 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 (M.op X4 X4)) X1))
       have i₂ := eq261 X1 X0 X4 X2 X3
       grind)
    | exact superpose eq261 eq271
    | exact resolve eq271 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq5703 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op X2 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op X2 X2)))) X1 X2
       have i₂ := eq261 (M.op X1 (M.op X2 X2)) X0 X5 X3 X4
       grind)
    | exact superpose eq261 eq9
    | exact resolve eq9 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5718 : ∀ X0 X1 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq5703 X0 X1 x X3 X4 X5
       have i₂ := eq1015 X1 x
       grind)
    | exact superpose eq1015 eq5703
    | exact resolve eq5703 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703
  have eq5727 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 (M.op X4 X4)) X1)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5680 X0 X1 X2 X3 X4 x
       have i₂ := eq1405 x
       grind)
    | exact superpose eq1405 eq5680
    | exact resolve eq5680 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5680
  have eq5775 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X4 X4)) = (M.op X1 (M.op (M.op (M.op X2 X2) (M.op (σ x) (σ y))) (M.op X0 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq5592 X0 X1 X2 x X4
       have i₂ := eq1015 (M.op X2 X2) x
       grind)
    | exact superpose eq1015 eq5592
    | exact resolve eq5592 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5592
  have eq5843 : ∀ X0 X1 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op x y)))) := by
    intro X0 X1 X3 X4 X5
    first
    | exact superpose eq1674 eq5718
    | exact resolve eq5718 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5718
  have eq5849 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 (M.op X4 X4)) X1)) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1674 eq5727
    | exact resolve eq5727 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5727
  have eq5873 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X4 X4)) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X4
    first
    | exact superpose eq1209 eq5775
    | exact resolve eq5775 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5775
  have eq5936 : ∀ X0 X1 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (M.op x y)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq5843 X0 X1 X3 X4 x
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq5843
    | exact resolve eq5843 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5843
  have eq5941 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5849 X0 X1 X2 X3 x
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq5849
    | exact resolve eq5849 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5849
  have eq5962 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X4 X4)) = (M.op X1 (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X4
    first
    | exact superpose eq1674 eq5873
    | exact resolve eq5873 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5873
  have eq6023 : ∀ X0 X1 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1 X3 X4
    first
    | exact superpose eq1674 eq5936
    | exact resolve eq5936 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5936
  have eq6028 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1674 eq5941
    | exact resolve eq5941 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5941
  have eq6046 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X1 (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5962 X0 X1 x
       have i₂ := eq1405 x
       grind)
    | exact superpose eq1405 eq5962
    | exact resolve eq5962 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5962
  have eq6105 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X3 X3) (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6023 X0 X1 X3 x
       have i₂ := eq1015 (M.op X3 X3) x
       grind)
    | exact superpose eq1015 eq6023
    | exact resolve eq6023 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6023
  have eq6110 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op (M.op X2 X2) (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6028 X0 X1 X2 x
       have i₂ := eq1015 (M.op X2 X2) x
       grind)
    | exact superpose eq1015 eq6028
    | exact resolve eq6028 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6028
  have eq6126 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq1674 eq6046
    | exact resolve eq6046 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6046
  have eq6181 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1209 eq6105
    | exact resolve eq6105 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6105
  have eq6186 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1209 eq6110
    | exact resolve eq6110 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6110
  have eq6237 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1674 eq6181
    | exact resolve eq6181 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6181
  have eq6242 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1674 eq6186
    | exact resolve eq6186 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6186
  have eq6603 : ∀ X0 X1 X2 X3 X4 X5 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op X2 X2)))) ∨ X0 = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq576 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2)))) X1 X2
       have i₂ := eq261 (M.op X1 (M.op X2 X2)) X1 X2 X3 X4
       grind)
    | exact superpose eq261 eq576
    | exact resolve eq576 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq6620 : ∀ X0 X1 X3 X4 X5 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op (σ x) (σ y))))) ∨ X0 = X1 := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq6603 X0 X1 x X3 X4 X5
       have i₂ := eq1015 X1 x
       grind)
    | exact superpose eq1015 eq6603
    | (have j0 := eq6603 (k X1 X0) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op (σ x) (σ y))))) x X3 X4 X5
       grind)
    | exact resolve eq6603 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6603
  have eq6675 : ∀ X0 X1 X3 X4 X5 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1 X3 X4 X5
    first
    | exact superpose eq1674 eq6620
    | (have j0 := eq6620 (k X1 X0) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op X5 X5)) (M.op X1 (M.op x y)))) X3 X4 X5
       grind)
    | exact resolve eq6620 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6620
  have eq6730 : ∀ X0 X1 X3 X4 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq6675 X0 X1 X3 X4 x
       have i₂ := eq1015 X0 x
       grind)
    | exact superpose eq1015 eq6675
    | (have j0 := eq6675 (k X1 X0) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (M.op x y)))) X3 X4 x
       grind)
    | exact resolve eq6675 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6675
  have eq6778 : ∀ X0 X1 X3 X4 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1 X3 X4
    first
    | exact superpose eq1674 eq6730
    | (have j0 := eq6730 (k X1 X0) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) X3 X4
       grind)
    | exact resolve eq6730 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6730
  have eq6821 : ∀ X0 X1 X3 : G, (k X1 X0) = (M.op (M.op (M.op X3 X3) (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6778 X0 X1 X3 x
       have i₂ := eq1015 (M.op X3 X3) x
       grind)
    | exact superpose eq1015 eq6778
    | (have j0 := eq6778 (k X1 X0) (M.op (M.op (M.op X3 X3) (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) X3 x
       grind)
    | exact resolve eq6778 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6778
  have eq6858 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq1209 eq6821
    | (have j0 := eq6821 (k X1 X0) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) x
       grind)
    | exact resolve eq6821 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6821
  have eq6895 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y)))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq1674 eq6858
    | (have j0 := eq6858 (k X1 X0) (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op x y))))
       grind)
    | exact resolve eq6858 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6858
  have eq6917 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq6237 eq6895
    | (have j0 := eq6895 (M.op X0 X1) (k X1 X0)
       grind)
    | exact resolve eq6895 eq6237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6237 eq6895
  have eq7286 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) = (M.op X3 (M.op (M.op x y) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq263 X3 X2 X0 X1 x x
       have i₂ := eq2700 (M.op x x)
       grind)
    | exact superpose eq2700 eq263
    | exact resolve eq263 eq2700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700
  have eq7539 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op X5 X5) (M.op X6 X6)) (M.op X2 (M.op X3 (M.op X4 X4)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X5 X5) (M.op X6 X6)) (M.op X2 (M.op X3 (M.op X4 X4)))) X3 X4
       have i₂ := eq263 (M.op X3 (M.op X4 X4)) X2 X0 X1 X5 X6
       grind)
    | exact superpose eq263 eq9
    | exact resolve eq9 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7557 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op X5 X5) (M.op X6 X6)) (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2 X3 X5 X6
    first
    | (have i₁ := eq7539 X0 X1 X2 X3 x X5 X6
       have i₂ := eq1015 X3 x
       grind)
    | exact superpose eq1015 eq7539
    | exact resolve eq7539 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7539
  have eq7782 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) X2) = (M.op X3 (M.op (M.op x y) (M.op X2 X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq7286 X0 x X2 X3
       have i₂ := eq1015 (M.op X0 X0) x
       grind)
    | exact superpose eq1015 eq7286
    | exact resolve eq7286 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7286
  have eq7893 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op X5 X5) (M.op X6 X6)) (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X0 X1 X2 X3 X5 X6
    first
    | exact superpose eq1674 eq7557
    | exact resolve eq7557 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7557
  have eq8053 : ∀ X2 X3 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op X3 (M.op (M.op x y) (M.op X2 X3))) := by
    intro X2 X3
    first
    | exact superpose eq1209 eq7782
    | exact resolve eq7782 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7782
  have eq8153 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op X5 X5) (M.op (σ x) (σ y))) (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq7893 X0 X1 X2 X3 X5 x
       have i₂ := eq1015 (M.op X5 X5) x
       grind)
    | exact superpose eq1015 eq7893
    | exact resolve eq7893 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7893
  have eq8298 : ∀ X2 X3 : G, (M.op (M.op x y) X2) = (M.op X3 (M.op (M.op x y) (M.op X2 X3))) := by
    intro X2 X3
    first
    | exact superpose eq1674 eq8053
    | exact resolve eq8053 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8053
  have eq8397 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1209 eq8153
    | exact resolve eq8153 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8153
  have eq8620 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op x y) (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1674 eq8397
    | exact resolve eq8397 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8397
  have eq8822 : ∀ X0 X2 X3 : G, (M.op (M.op x y) (M.op X2 (M.op X3 (M.op x y)))) = (M.op (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq8620 X0 x X2 X3
       have i₂ := eq1015 (M.op X0 X0) x
       grind)
    | exact superpose eq1015 eq8620
    | exact resolve eq8620 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8620
  have eq8987 : ∀ X2 X3 : G, (M.op (M.op x y) (M.op X2 (M.op X3 (M.op x y)))) = (M.op (M.op (M.op (σ x) (σ y)) X2) X3) := by
    intro X2 X3
    first
    | exact superpose eq1209 eq8822
    | exact resolve eq8822 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8822
  have eq9079 : ∀ X2 X3 : G, (M.op (M.op x y) (M.op X2 (M.op X3 (M.op x y)))) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X2 X3
    first
    | exact superpose eq1674 eq8987
    | exact resolve eq8987 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8987
  have eq10124 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1333 eq1131
    | exact resolve eq1131 eq1333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq1333
  have eq10660 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X2 (M.op (M.op (σ x) (σ y)) X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1531 X0 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X1 (M.op sF6 X0)))
       have i₂ := eq263 (M.op sF6 X0) X1 X2 X3 X4 X5
       grind)
    | exact superpose eq263 eq1531
    | exact resolve eq1531 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10715 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op (M.op (σ x) (σ y)) X3) X0)) = (M.op X3 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq1531 eq263
    | exact resolve eq263 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq1531
  have eq10768 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op (M.op (σ x) (σ y)) X3) X0)) = (M.op X3 (M.op (M.op (M.op X4 X4) (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10715 X0 X1 X2 X3 X4 x
       have i₂ := eq1015 (M.op X4 X4) x
       grind)
    | exact superpose eq1015 eq10715
    | exact resolve eq10715 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10715
  have eq10814 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq1674 eq10660
    | exact resolve eq10660 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10660
  have eq10849 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op (M.op (σ x) (σ y)) X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1209 eq10768
    | exact resolve eq10768 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10768
  have eq10872 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (M.op X4 X4) (M.op (σ x) (σ y))) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10814 X0 X1 X2 X3 X4 x
       have i₂ := eq1015 (M.op X4 X4) x
       grind)
    | exact superpose eq1015 eq10814
    | exact resolve eq10814 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10814
  have eq10893 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op (M.op x y) X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1674 eq10849
    | exact resolve eq10849 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10849
  have eq10911 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1209 eq10872
    | exact resolve eq10872 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10872
  have eq10928 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X1) (M.op (σ x) (σ y))) (M.op (M.op (M.op x y) X3) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq10893 X0 X1 x X3
       have i₂ := eq1015 (M.op X1 X1) x
       grind)
    | exact superpose eq1015 eq10893
    | exact resolve eq10893 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10893
  have eq10942 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) = (M.op (M.op x y) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1674 eq10911
    | exact resolve eq10911 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10911
  have eq10954 : ∀ X0 X3 : G, (M.op X3 (M.op (M.op x y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op x y) X3) X0)) := by
    intro X0 X3
    first
    | exact superpose eq1209 eq10928
    | exact resolve eq10928 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10928
  have eq10965 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) X2) X3) = (M.op (M.op x y) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq10942 X0 x X2 X3
       have i₂ := eq1015 (M.op X0 X0) x
       grind)
    | exact superpose eq1015 eq10942
    | exact resolve eq10942 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10942
  have eq10974 : ∀ X0 X3 : G, (M.op X3 (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op (M.op x y) X3) X0)) := by
    intro X0 X3
    first
    | exact superpose eq1674 eq10954
    | exact resolve eq10954 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10954
  have eq10980 : ∀ X2 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) X2) X3) = (M.op (M.op x y) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X2 X3
    first
    | exact superpose eq1209 eq10965
    | exact resolve eq10965 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209 eq10965
  have eq10990 : ∀ X2 X3 : G, (M.op (M.op (M.op x y) X2) X3) = (M.op (M.op x y) (M.op X2 (M.op (M.op x y) X3))) := by
    intro X2 X3
    first
    | exact superpose eq1674 eq10980
    | exact resolve eq10980 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10980
  have eq12200 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) (M.op (M.op X2 (M.op X3 X3)) X0))) = X2 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1006 eq261
    | exact resolve eq261 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq1006
  have eq12263 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) (M.op (M.op X2 (M.op (σ x) (σ y))) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12200 X0 X1 X2 x
       have i₂ := eq1015 X2 x
       grind)
    | exact superpose eq1015 eq12200
    | exact resolve eq12200 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12200
  have eq12363 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op x y) (M.op X1 X1)) (M.op (M.op X2 (M.op x y)) X0))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq1674 eq12263
    | exact resolve eq12263 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12263
  have eq12423 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op X1 X1) (M.op (M.op x y) (M.op (M.op X2 (M.op x y)) X0))))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq10990 eq12363
    | exact resolve eq12363 eq10990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12363
  have eq12468 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op X1 X1) (M.op X2 (M.op (M.op x y) X0))))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq6242 eq12423
    | exact resolve eq12423 eq6242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6242 eq12423
  have eq12503 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op (M.op x y) X0))))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq12468 X0 x X2
       have i₂ := eq1405 x
       grind)
    | exact superpose eq1405 eq12468
    | exact resolve eq12468 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12468
  have eq12527 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) X0))))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq1674 eq12503
    | exact resolve eq12503 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12503
  have eq12544 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op (M.op x y) X0))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq1941 eq12527
    | exact resolve eq12527 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12527
  have eq28914 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1751 eq12544
    | exact resolve eq12544 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq36507 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) X0) = (M.op (M.op (M.op x y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq10124 eq28914
    | exact resolve eq28914 eq10124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10124
  have eq36533 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op X0 X1) (M.op x y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq28914 eq28914
    | exact resolve eq28914 eq28914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28914
  have eq36882 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) X0) = (M.op (M.op x y) (M.op X1 (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq10990 eq36507
    | exact resolve eq36507 eq10990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10990 eq36507
  have eq41636 : ∀ X0 : G, (k (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq5178 eq6917
    | (have j0 := eq6917 (k (M.op x y) X0) (k X0 (M.op x y))
       have j1 := eq5178 X0
       grind)
    | exact resolve eq6917 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41692 : ∀ X0 : G, (k (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have j0 := eq41636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41636
  have eq43069 : (τ (k (M.op x y) (σ (M.op x y)))) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41692 eq68
    | (have j1 := eq41692 (σ (M.op x y))
       grind)
    | exact resolve eq68 eq41692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq41692
  have eq43080 : (τ (k (M.op x y) (σ (M.op x y)))) = (k (M.op x y) (τ (M.op x y))) := by
    first
    | (have r₁ := eq43069
       have r₂ := eq1753
       grind)
    | exact resolve eq43069 eq1753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43069
  have eq43089 : (k (τ (M.op x y)) (M.op x y)) = (k (M.op x y) (τ (M.op x y))) := by
    first
    | exact superpose eq88 eq43080
    | exact resolve eq43080 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43080
  have eq43103 : (k (σ (τ (M.op x y))) (σ (M.op x y))) = (σ (k (M.op x y) (τ (M.op x y)))) := by
    first
    | exact superpose eq43089 eq15
    | exact resolve eq15 eq43089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43104 : (k (σ (τ (M.op x y))) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (τ (M.op x y)))) := by
    first
    | (have i₁ := eq43103
       have i₂ := eq15 sF2 (τ sF2)
       grind)
    | exact superpose eq15 eq43103
    | exact resolve eq43103 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43103
  have eq43107 : (k (M.op x y) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq43104
       have i₂ := eq36 sF2
       grind)
    | exact superpose eq36 eq43104
    | exact resolve eq43104 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43104
  have eq43109 : (k (σ (M.op x y)) (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq43107
    | exact resolve eq43107 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43107
  have eq52420 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op (M.op x y) (k X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6126 X1 X0
       have i₂ := eq6917 X1 X0
       grind)
    | exact superpose eq6917 eq6126
    | (have j1 := eq6917 (M.op X1 (M.op x y)) (M.op X0 (M.op (M.op x y) (k X0 X1)))
       grind)
    | exact resolve eq6126 eq6917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6126 eq6917
  have eq80809 : (σ (M.op x y)) = (M.op (k (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq43109 eq5033
    | (have j0 := eq5033 (σ (M.op x y)) (M.op (k (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq5033 eq43109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5033
  have eq80995 : (σ (M.op x y)) = (M.op (k (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq80809
       have r₂ := eq1753
       grind)
    | exact resolve eq80809 eq1753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753 eq80809
  have eq81052 : (σ (M.op x y)) = (M.op (k (M.op x y) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq80995
       have i₂ := eq1015 (k sF2 sF3) sF2
       grind)
    | exact superpose eq1015 eq80995
    | exact resolve eq80995 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq80995
  have eq81091 : (σ (M.op x y)) = (M.op (k (M.op x y) (σ (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq1674 eq81052
    | exact resolve eq81052 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81052
  have eq81200 : (σ (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (σ (M.op x y)))) := by
    first
    | exact superpose eq81091 eq1726
    | exact resolve eq1726 eq81091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq81203 : (σ (M.op x y)) = (k (k (M.op x y) (σ (M.op x y))) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq81091 eq5178
    | (have j0 := eq5178 (k (M.op x y) (σ (M.op x y)))
       grind)
    | exact resolve eq5178 eq81091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178 eq81091
  have eq123609 : (τ (σ (M.op x y))) = (k (τ (k (M.op x y) (σ (M.op x y)))) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq81203 eq142
    | exact resolve eq142 eq81203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq81203
  have eq123627 : (τ (σ (M.op x y))) = (k (k (τ (M.op x y)) (M.op x y)) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq88 eq123609
    | exact resolve eq123609 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq123609
  have eq123635 : (τ (σ (M.op x y))) = (k (k (M.op x y) (τ (M.op x y))) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq43089 eq123627
    | exact resolve eq123627 eq43089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43089 eq123627
  have eq123642 : (M.op x y) = (k (k (M.op x y) (τ (M.op x y))) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq37 eq123635
    | exact resolve eq123635 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq123635
  have eq134918 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1))) := by
    intro X0 X1
    first
    | exact superpose eq9079 eq8298
    | exact resolve eq8298 eq9079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8298 eq9079
  have eq135611 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op X0 (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq10974 eq134918
    | exact resolve eq134918 eq10974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10974 eq134918
  have eq136061 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op X0 (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq135611 X0 X1
       have i₂ := eq1405 sF2
       grind)
    | exact superpose eq1405 eq135611
    | exact resolve eq135611 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135611
  have eq136409 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op X0 (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq1674 eq136061
    | exact resolve eq136061 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674 eq136061
  have eq216662 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq136409 eq36533
    | exact resolve eq36533 eq136409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36533 eq136409
  have eq216666 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op X1 (M.op x y)))))) := by
    intro X0 X1
    first
    | exact superpose eq36882 eq216662
    | exact resolve eq216662 eq36882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36882 eq216662
  have eq217078 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op X1 (M.op x y)))) = (M.op (M.op X0 (M.op (M.op x y) X1)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1941 eq216666
    | exact resolve eq216666 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941 eq216666
  have eq240745 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) (k X0 X1))) (M.op x y)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1749 X0
       have i₂ := eq52420 (M.op X0 sF2) X1
       grind)
    | exact superpose eq52420 eq1749
    | (have j1 := eq52420 (M.op (M.op X0 (M.op (M.op x y) (k X0 X1))) (M.op x y)) X1
       grind)
    | exact resolve eq1749 eq52420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749 eq52420
  have eq241356 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op (k X0 X1) (M.op x y)))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq217078 eq240745
    | (have j0 := eq240745 (M.op (M.op x y) (M.op X0 (M.op (k X0 X1) (M.op x y)))) X1
       grind)
    | exact resolve eq240745 eq217078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217078 eq240745
  have eq389671 : (τ (M.op x y)) = (M.op (M.op x y) (M.op (k (M.op x y) (τ (M.op x y))) (M.op (M.op x y) (M.op x y)))) ∨ (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq123642 eq241356
    | (have j0 := eq241356 (τ (M.op x y)) (M.op (M.op x y) (M.op (k (M.op x y) (τ (M.op x y))) (M.op (M.op x y) (M.op x y))))
       grind)
    | exact resolve eq241356 eq123642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123642 eq241356
  have eq389683 : (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq389671
       have i₂ := eq12544 x (M.op sF2 (M.op (k sF2 (τ sF2)) (M.op sF2 sF2)))
       grind)
    | exact superpose eq12544 eq389671
    | exact resolve eq389671 eq12544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12544 eq389671
  have eq389684 : (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by grind
  clear eq389683
  have eq389742 : (σ (τ (M.op x y))) = (k (σ (M.op x y)) (σ (τ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq389684 eq15
    | exact resolve eq15 eq389684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389684
  have eq389780 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq389742
       have i₂ := eq36 sF2
       grind)
    | exact superpose eq36 eq389742
    | exact resolve eq389742 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq389742
  have eq389795 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq389780
    | exact resolve eq389780 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq389780
  have eq389796 : (M.op x y) = (k (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq43109 eq389795
    | exact resolve eq389795 eq43109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43109 eq389795
  have eq389797 : (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by grind
  clear eq389796
  have eq390443 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq389797 eq81200
    | exact resolve eq81200 eq389797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81200 eq389797
  have eq390614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq390443
       have i₂ := eq1405 sF2
       grind)
    | exact superpose eq1405 eq390443
    | exact resolve eq390443 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405 eq390443
  have eq390666 : False := by grind
  exact eq390666

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pyx_pxy_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq15
    | exact resolve eq15 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq64
    | exact resolve eq64 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq64
  have eq89 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X1 (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq89
    | (have j0 := eq89 X1 (σ X0)
       grind)
    | (have r₁ := eq89 X0 (σ X0)
       have r₂ := eq75 X0
       grind)
    | exact resolve eq89 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq381 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq376 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq376
    | (have j0 := eq376 X0 X1
       grind)
    | exact resolve eq376 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq2995 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq3108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2995 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq2995
    | (have j0 := eq2995 X0 X1
       grind)
    | exact resolve eq2995 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995
  have eq3160 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3108 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq3108
    | (have j0 := eq3108 X0 X1
       grind)
    | exact resolve eq3108 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq3108
  have eq3176 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3160 X0 X1
       have j1 := eq381 X1 X0
       grind)
    | (have r₁ := eq3160 X0 X1
       have r₂ := eq381 X0 X1
       grind)
    | (have r₁ := eq3160 X1 X0
       have r₂ := eq381 X0 X1
       grind)
    | exact resolve eq3160 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq3160
  have eq3196 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3176 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3176
    | exact resolve eq3176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176
  have eq3222 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3196 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq3196
    | (have j0 := eq3196 X0 X1
       grind)
    | exact resolve eq3196 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196
  have eq3260 : ∀ X0 X1 : G, (M.op (τ X1) (σ X0)) = (M.op (σ X0) (τ X1)) ∨ (k X1 (σ (σ X0))) = (σ (M.op (σ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (σ X0)
       have i₂ := eq3222 (τ X1) X0
       grind)
    | exact superpose eq3222 eq17
    | (have j1 := eq3222 (τ X1) X0
       grind)
    | exact resolve eq17 eq3222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3222
  have eq10532 : ∀ X0 X1 : G, (M.op (σ X0) (τ X1)) ≠ (M.op (σ X0) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (τ X1) (τ X1)) ∨ (k (τ X1) (σ X0)) = (M.op (σ X0) (τ X1)) ∨ (k X1 (σ (σ X0))) = (σ (M.op (σ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (σ X0)
       have i₂ := eq3260 X0 X1
       grind)
    | exact superpose eq3260 eq13
    | (have j0 := eq13 (σ X0) (τ X1)
       have j1 := eq3260 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (τ X1)
       have r₂ := eq3260 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (σ X0)
       have r₂ := eq3260 X0 X1
       grind)
    | exact resolve eq13 eq3260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260
  have eq10540 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (τ X1) (τ X1)) ∨ (k (τ X1) (σ X0)) = (M.op (σ X0) (τ X1)) ∨ (k X1 (σ (σ X0))) = (σ (M.op (σ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq10532 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10532
  have eq10544 : ∀ X0 X1 : G, (k X1 (σ (σ X0))) = (σ (M.op (σ X0) (τ X1))) ∨ (k (τ X1) (σ X0)) = (M.op (σ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10540 X0 X1
       have j1 := eq12 (τ X1) (σ X0)
       grind)
    | (have r₁ := eq10540 X0 X1
       have r₂ := eq12 (σ X0) (τ X1)
       grind)
    | (have r₁ := eq10540 X0 X1
       have r₂ := eq12 (τ X1) (σ X0)
       grind)
    | exact resolve eq10540 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10540
  have eq24772 : ∀ X0 X1 : G, (M.op (σ X1) (τ X0)) = (τ (k X0 (σ (σ X1)))) ∨ (k (τ X0) (σ X1)) = (M.op (σ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X1) (τ X0))
       have i₂ := eq10544 X1 X0
       grind)
    | exact superpose eq10544 eq10
    | (have j1 := eq10544 X1 X0
       grind)
    | exact resolve eq10 eq10544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10544
  have eq24833 : ∀ X0 X1 : G, (k (τ X0) (σ X1)) = (M.op (σ X1) (τ X0)) ∨ (k (τ X0) (σ X1)) = (M.op (σ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24772 X0 X1
       have i₂ := eq22 X0 (σ X1)
       grind)
    | exact superpose eq22 eq24772
    | (have j0 := eq24772 X0 X1
       grind)
    | exact resolve eq24772 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24772
  have eq24834 : ∀ X0 X1 : G, (k (τ X0) (σ X1)) = (M.op (σ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq24833 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24833
  have eq24859 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24834 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24834
    | exact resolve eq24834 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24834
  have eq25039 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24859 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24859
    | exact resolve eq24859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25113 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq24859 (σ X1) X0
       grind)
    | exact superpose eq24859 eq15
    | exact resolve eq15 eq24859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24859
  have eq26896 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25113 x y
       grind)
    | exact superpose eq25113 eq16
    | exact resolve eq16 eq25113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25113
  have eq27013 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq26896
       have i₂ := eq25039 x y
       grind)
    | exact superpose eq25039 eq26896
    | exact resolve eq26896 eq25039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25039 eq26896
  have eq27014 : False := by grind
  exact eq27014

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_x_pyx_x_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq70 : y ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ y = (k y x) := by
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
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq104 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq79
    | (have j0 := eq79 (σ y) (σ X0)
       grind)
    | exact resolve eq79 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq85
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq85 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq140 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq155 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120 eq79
    | (have j0 := eq79 (σ y) (σ x)
       grind)
    | exact resolve eq79 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq189
    | exact resolve eq189 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq193 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq190
       have r₂ := eq27
       grind)
    | exact resolve eq190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq195 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq193
    | exact resolve eq193 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq197 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq195 eq27
    | exact resolve eq27 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq195 eq71
    | (have r₁ := eq71
       have r₂ := eq195
       grind)
    | exact resolve eq71 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq195
  have eq472 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq471
  have eq475 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq472 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq472
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq472
       grind)
    | exact resolve eq13 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq1871 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq475 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq1874 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1871
    | exact resolve eq1871 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871
  have eq1880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120 eq1874
    | exact resolve eq1874 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1874
  have eq1888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1880
  have eq1891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1888
       have r₂ := eq197
       grind)
    | exact resolve eq1888 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq1888
  have eq1892 : y = (M.op x y) := by
    first
    | (have r₁ := eq1891
       have r₂ := eq27
       grind)
    | exact resolve eq1891 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891
  have eq1893 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1892 eq20
    | exact resolve eq20 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1895 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (k y x) := by
    first
    | exact superpose eq1892 eq70
    | (have r₁ := eq70
       have r₂ := eq1892
       grind)
    | exact resolve eq70 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1904 : (M.op x x) = (M.op y y) ∨ y = (k y x) := by grind
  clear eq1895
  have eq1914 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1893
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1893
    | exact resolve eq1893 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq1992 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1914 eq26
    | exact resolve eq26 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2138 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1904
       grind)
    | exact superpose eq1904 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1904
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1904
       grind)
    | exact resolve eq13 eq1904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq2603 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1914 eq104
    | (have j0 := eq104 X0
       grind)
    | exact resolve eq104 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq2604 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1914 eq2603
    | (have j0 := eq2603 X0
       grind)
    | exact resolve eq2603 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2678 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2604 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2604
    | (have j0 := eq2604 x
       grind)
    | exact resolve eq2604 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2604
  have eq2686 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1992 eq2678
    | exact resolve eq2678 eq1992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678
  have eq2710 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2686
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq2686
    | exact resolve eq2686 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq2686
  have eq2728 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1914 eq2710
    | exact resolve eq2710 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710
  have eq2736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1992 eq2728
    | exact resolve eq2728 eq1992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992 eq2728
  have eq2740 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq2736
       have r₂ := eq27
       grind)
    | exact resolve eq2736 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736
  have eq2748 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq2740 eq155
    | exact resolve eq155 eq2740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq2740
  have eq2751 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1892 eq2748
    | exact resolve eq2748 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq575725 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2138 X0
       have i₂ := eq2751
       grind)
    | exact superpose eq2751 eq2138
    | (have j0 := eq2138 X0
       grind)
    | exact resolve eq2138 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138
  have eq575739 : y = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y x) := by
    first
    | (have j0 := eq575725 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575725
  have eq575742 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq575739
       have i₂ := eq2751
       grind)
    | exact superpose eq2751 eq575739
    | exact resolve eq575739 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751 eq575739
  have eq575750 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq575742
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq575742
    | exact resolve eq575742 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq575742
  have eq575755 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1892 eq575750
    | exact resolve eq575750 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892 eq575750
  have eq575756 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq575755
  have eq576394 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq575756 eq15
    | exact resolve eq15 eq575756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575756
  have eq576933 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq576394
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq576394
    | exact resolve eq576394 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq576394
  have eq577027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1914 eq576933
    | exact resolve eq576933 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914 eq576933
  have eq577063 : False := by grind
  exact eq577063

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxy_y_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq45 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
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
  have eq84 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  have eq142 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq564 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq600 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq564
    | (have j0 := eq564 X0 X1
       grind)
    | exact resolve eq564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq798 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X0))) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq142 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq142
    | (have j0 := eq142 (σ X0) (σ X1)
       grind)
    | exact resolve eq142 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq3635 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq82 X1 X0
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq82 X0 (σ X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (σ X0) (σ X0))
       have r₂ := eq82 X0 (M.op X0 (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3636 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq82 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq3637 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3636
  have eq3638 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3635 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3635
  have eq3639 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3638 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq3642 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3637 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3637
    | (have j0 := eq3637 X0
       grind)
    | exact resolve eq3637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq3680 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq3642 X0
       grind)
    | exact superpose eq3642 eq45
    | (have j1 := eq3642 X0
       grind)
    | exact resolve eq45 eq3642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3642
  have eq3696 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3680 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3680
    | (have j0 := eq3680 X0
       grind)
    | exact resolve eq3680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3680
  have eq3697 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3696 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696
  have eq3699 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3697 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3697
    | exact resolve eq3697 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3723 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3697 X0
       grind)
    | exact superpose eq3697 eq11
    | exact resolve eq11 eq3697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3697
  have eq3768 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3699 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq3699
    | exact resolve eq3699 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3699
  have eq3868 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3768 X0
       grind)
    | exact superpose eq3768 eq11
    | exact resolve eq11 eq3768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3768
  have eq3944 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3868 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3868
    | exact resolve eq3868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868
  have eq4565 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    grind
  have eq4582 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4565 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq4565
    | exact resolve eq4565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4565
  have eq4620 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4582 X0
       have i₂ := eq3944 X0
       grind)
    | exact superpose eq3944 eq4582
    | exact resolve eq4582 eq3944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4582
  have eq4636 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq4620
  have eq28973 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq798 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq798
    | (have j0 := eq798 (τ X0) (τ X1)
       grind)
    | exact resolve eq798 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq798
  have eq29087 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28973 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq28973
    | (have j0 := eq28973 X0 X1
       grind)
    | exact resolve eq28973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28973
  have eq29175 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29087 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29087
    | (have j0 := eq29087 X0 X1
       grind)
    | exact resolve eq29087 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29087
  have eq29262 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29175 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29175
    | (have j0 := eq29175 X0 X1
       grind)
    | exact resolve eq29175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29175
  have eq29342 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29262 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29262
    | (have j0 := eq29262 X0 X1
       grind)
    | exact resolve eq29262 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29262
  have eq29412 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29342 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29342
    | (have j0 := eq29342 X0 X1
       grind)
    | exact resolve eq29342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29342
  have eq29473 : ∀ X0 X1 : G, (σ X1) = (σ (k (σ (τ X0)) (σ (τ X0)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29412 X0 X1
       have i₂ := eq3723 (σ (τ X0))
       grind)
    | exact superpose eq3723 eq29412
    | (have j0 := eq29412 X0 X1
       grind)
    | exact resolve eq29412 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29412
  have eq29522 : ∀ X0 X1 : G, (σ X1) = (σ (σ (k (τ X0) (τ X0)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29473 X0 X1
       have i₂ := eq15 (τ X0) (τ X0)
       grind)
    | exact superpose eq15 eq29473
    | (have j0 := eq29473 X0 X1
       grind)
    | exact resolve eq29473 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29473
  have eq29563 : ∀ X0 X1 : G, (σ X1) = (σ (k (σ (τ X0)) X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29522 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq29522
    | (have j0 := eq29522 X0 X1
       grind)
    | exact resolve eq29522 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29522
  have eq29593 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29563 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29563
    | (have j0 := eq29563 X0 X1
       grind)
    | exact resolve eq29563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29563
  have eq29621 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29593 X0 X1
       have i₂ := eq3944 X0
       grind)
    | exact superpose eq3944 eq29593
    | (have j0 := eq29593 X0 X1
       grind)
    | exact resolve eq29593 eq3944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29593
  have eq70201 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq3639 (σ X0) X1
       grind)
    | exact superpose eq3639 eq23
    | (have j1 := eq3639 (σ X0) X1
       grind)
    | exact resolve eq23 eq3639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3639
  have eq70323 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq70201 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq70201
    | (have j0 := eq70201 X0 X1
       grind)
    | exact resolve eq70201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70201
  have eq70440 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq70323 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70323
    | (have j0 := eq70323 X0 X1
       grind)
    | exact resolve eq70323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70323
  have eq70553 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq70440 X0 X1
       have i₂ := eq3723 X1
       grind)
    | exact superpose eq3723 eq70440
    | (have j0 := eq70440 X0 X1
       grind)
    | exact resolve eq70440 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723 eq70440
  have eq70642 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq70553 X0 X1
       have i₂ := eq3944 X1
       grind)
    | exact superpose eq3944 eq70553
    | (have j0 := eq70553 X0 X1
       grind)
    | exact resolve eq70553 eq3944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3944 eq70553
  have eq70702 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70642 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70642
    | (have j0 := eq70642 X0 X1
       grind)
    | exact resolve eq70642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70642
  have eq74012 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq70702 X1 X0
       grind)
    | exact superpose eq70702 eq11
    | (have j1 := eq70702 X1 X0
       grind)
    | exact resolve eq11 eq70702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70702
  have eq74676 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74012 x y
       grind)
    | exact superpose eq74012 eq16
    | (have j1 := eq74012 x y
       grind)
    | exact resolve eq16 eq74012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74012
  have eq76447 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74676
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq74676
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq74676 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76448 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74676
       have i₂ := eq600 x y
       grind)
    | exact superpose eq600 eq74676
    | (have j1 := eq600 x y
       grind)
    | (have r₁ := eq74676
       have r₂ := eq600 x y
       grind)
    | exact resolve eq74676 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq74676
  have eq76449 : (σ y) = (σ (M.op x x)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq76448
  have eq76450 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq76447
  have eq76451 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq76450
  have eq76453 : y = (k x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq76449
       have r₂ := eq13 x y
       grind)
    | exact resolve eq76449 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76449
  have eq77875 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29621 x y
       have i₂ := eq76453
       grind)
    | exact superpose eq76453 eq29621
    | (have j0 := eq29621 x y
       grind)
    | exact resolve eq29621 eq76453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29621 eq76453
  have eq77880 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq77875
  have eq77881 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq77880
  have eq77900 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77881
       grind)
    | exact superpose eq77881 eq16
    | exact resolve eq16 eq77881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77881
  have eq78402 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77900
       have i₂ := eq76451
       grind)
    | exact superpose eq76451 eq77900
    | exact resolve eq77900 eq76451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76451 eq77900
  have eq78406 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq78402
  have eq78407 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq78406
  have eq78431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4636 x
       have i₂ := eq78407
       grind)
    | exact superpose eq78407 eq4636
    | exact resolve eq4636 eq78407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78407
  have eq78485 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq78431
       have r₂ := eq16
       grind)
    | exact resolve eq78431 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78431
  have eq79014 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq78485
       grind)
    | exact superpose eq78485 eq10
    | exact resolve eq10 eq78485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78485
  have eq79192 : y = (M.op x x) := by
    first
    | (have i₁ := eq79014
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq79014
    | exact resolve eq79014 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79014
  have eq79330 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4636 x
       have i₂ := eq79192
       grind)
    | exact superpose eq79192 eq4636
    | exact resolve eq4636 eq79192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4636 eq79192
  have eq79384 : False := by grind
  exact eq79384

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_pyy_pyx_pyy_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq263 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq263 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq263 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq263 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq275 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq264 (σ X0)
       grind)
    | exact superpose eq264 eq15
    | exact resolve eq15 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq264 (τ X0)
       grind)
    | exact superpose eq264 eq31
    | exact resolve eq31 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq281
    | exact resolve eq281 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq294 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq275
    | exact resolve eq275 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq275
  have eq439 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq456 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq439
    | (have j0 := eq439 X0 X1
       grind)
    | exact resolve eq439 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq735 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq456 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq456
    | exact resolve eq456 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq775 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq735
    | (have j0 := eq735 X0 X1
       grind)
    | exact resolve eq735 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq735
  have eq777 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq775 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq775 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq775 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq775 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq778 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq777 X0 X1
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq777
    | (have j0 := eq777 X0 X1
       grind)
    | exact resolve eq777 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq779 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq778 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq778
    | (have j0 := eq778 X0 X1
       grind)
    | exact resolve eq778 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq780 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq779 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq779
    | exact resolve eq779 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq779 (σ X0) X1
       grind)
    | exact superpose eq779 eq15
    | (have j1 := eq779 (σ X0) X1
       grind)
    | exact resolve eq15 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq817 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq789 X0 X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq789
    | (have j0 := eq789 X0 X1
       grind)
    | exact resolve eq789 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq852 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq780 (τ X1) X0
       grind)
    | exact superpose eq780 eq17
    | (have j1 := eq780 (τ X1) X0
       grind)
    | exact resolve eq17 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq780
  have eq1011 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq852 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq852
    | exact resolve eq852 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq1061 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1011 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1011
    | (have j0 := eq1011 X0 X1
       grind)
    | exact resolve eq1011 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq2534 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq817 x y
       grind)
    | exact superpose eq817 eq16
    | (have j1 := eq817 x y
       grind)
    | exact resolve eq16 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2552 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq817 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq2581 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2534
       have i₂ := eq1061 y x
       grind)
    | exact superpose eq1061 eq2534
    | (have j1 := eq1061 y x
       grind)
    | (have r₁ := eq2534
       have r₂ := eq1061 y x
       grind)
    | exact resolve eq2534 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061 eq2534
  have eq2582 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2581
  have eq2585 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2582
       grind)
    | exact superpose eq2582 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2582
       grind)
    | exact resolve eq13 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2587 : x = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2585
  have eq2598 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2552 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2552
    | (have j0 := eq2552 (τ X1) (τ X0)
       grind)
    | exact resolve eq2552 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2643 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2598 X0 X1
       have i₂ := eq288 X1
       grind)
    | exact superpose eq288 eq2598
    | (have j0 := eq2598 X0 X1
       grind)
    | exact resolve eq2598 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq2663 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2643 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq2643
    | (have j0 := eq2643 X0 X1
       grind)
    | exact resolve eq2643 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2643
  have eq2677 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2663 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2663
    | (have j0 := eq2663 X0 X1
       grind)
    | exact resolve eq2663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq2689 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2677 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2677
    | (have j0 := eq2677 X0 X1
       grind)
    | exact resolve eq2677 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2677
  have eq2696 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2689 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2689
    | (have j0 := eq2689 X0 X1
       grind)
    | exact resolve eq2689 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689
  have eq2702 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X1 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2696 X0 X1
       have i₂ := eq288 X1
       grind)
    | exact superpose eq288 eq2696
    | (have j0 := eq2696 X0 X1
       grind)
    | exact resolve eq2696 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq2696
  have eq2703 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2702 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq2702
    | (have j0 := eq2702 X0 X1
       grind)
    | exact resolve eq2702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq8997 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2587
       grind)
    | exact superpose eq2587 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2587
       grind)
    | exact resolve eq12 eq2587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq8998 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq8997
  have eq40178 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8998
       grind)
    | exact superpose eq8998 eq16
    | exact resolve eq16 eq8998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8998
  have eq40212 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq40178
       have i₂ := eq2582
       grind)
    | exact superpose eq2582 eq40178
    | exact resolve eq40178 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582 eq40178
  have eq40237 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq40212
  have eq40238 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq40237
  have eq40262 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq40238
       grind)
    | exact superpose eq40238 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq40238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40280 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq40262
       have r₂ := eq294 x
       grind)
    | exact resolve eq40262 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40262
  have eq40282 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq40280
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq40280
    | exact resolve eq40280 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40280
  have eq40283 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq40282
       have i₂ := eq294 x
       grind)
    | exact superpose eq294 eq40282
    | exact resolve eq40282 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq40282
  have eq111498 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq40283
       grind)
    | exact superpose eq40283 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq40283
       grind)
    | exact resolve eq12 eq40283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40283
  have eq111510 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq111498
  have eq111522 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq111510
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq111510
    | exact resolve eq111510 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111510
  have eq936138 : (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq40238
       have i₂ := eq111522
       grind)
    | exact superpose eq111522 eq40238
    | exact resolve eq40238 eq111522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40238 eq111522
  have eq936393 : (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq936138
  have eq936858 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2552 x y
       have i₂ := eq936393
       grind)
    | exact superpose eq936393 eq2552
    | (have j0 := eq2552 x y
       grind)
    | (have r₁ := eq2552 x y
       have r₂ := eq936393
       grind)
    | exact resolve eq2552 eq936393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936860 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2703 y x
       have i₂ := eq936393
       grind)
    | exact superpose eq936393 eq2703
    | (have j0 := eq2703 y x
       grind)
    | (have r₁ := eq2703 y x
       have r₂ := eq936393
       grind)
    | exact resolve eq2703 eq936393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936393
  have eq937088 : (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq936860
  have eq937090 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq936858
  have eq937096 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq2552 x y
       grind)
    | (have r₁ := eq937090
       have r₂ := eq2552 x y
       grind)
    | exact resolve eq937090 eq2552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552 eq937090
  have eq937150 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq937096
       grind)
    | exact superpose eq937096 eq16
    | exact resolve eq16 eq937096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937096
  have eq937616 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq937150
       have i₂ := eq937088
       grind)
    | exact superpose eq937088 eq937150
    | exact resolve eq937150 eq937088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937088
  have eq937626 : (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq937616
  have eq937771 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq937626
       grind)
    | exact superpose eq937626 eq10
    | exact resolve eq10 eq937626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937626
  have eq938494 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq937771
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq937771
    | exact resolve eq937771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937771
  have eq939117 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2703 y x
       have i₂ := eq938494
       grind)
    | exact superpose eq938494 eq2703
    | (have j0 := eq2703 y x
       grind)
    | (have r₁ := eq2703 y x
       have r₂ := eq938494
       grind)
    | exact resolve eq2703 eq938494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703 eq938494
  have eq939345 : (M.op x y) = (M.op x x) := by grind
  clear eq939117
  have eq939480 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq937150
       have i₂ := eq939345
       grind)
    | exact superpose eq939345 eq937150
    | exact resolve eq937150 eq939345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937150 eq939345
  have eq939490 : False := by grind
  exact eq939490

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
  have eq74 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1
       have i₂ := eq38 X1
       grind)
    | exact superpose eq38 eq80
    | (have j0 := eq80 X0 X1
       grind)
    | exact resolve eq80 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq80
  have eq120 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq143 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq120
    | (have j0 := eq120 X0 X1
       grind)
    | exact resolve eq120 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq120
  have eq149 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq143 X1 X0
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq143 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq143
  have eq331 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq149
    | exact resolve eq149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq149 (σ X0) X1
       grind)
    | exact superpose eq149 eq15
    | (have j1 := eq149 (σ X0) X1
       grind)
    | exact resolve eq15 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq360 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq331 (τ X1) X0
       grind)
    | exact superpose eq331 eq18
    | (have j1 := eq331 (τ X1) X0
       grind)
    | exact resolve eq18 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq331
  have eq417 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq447 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq417
    | (have j0 := eq417 X0 X1
       grind)
    | exact resolve eq417 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq802 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq360
    | exact resolve eq360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq859 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq802 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq802
    | (have j0 := eq802 X0 X1
       grind)
    | exact resolve eq802 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq1490 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq341 x y
       grind)
    | exact superpose eq341 eq16
    | (have j1 := eq341 x y
       grind)
    | exact resolve eq16 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1509 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq341 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq8185 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq447 X0 X1
       grind)
    | exact superpose eq447 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq447 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq447 X0 X1
       grind)
    | exact resolve eq13 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq8210 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8185
  have eq8211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq8210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8210
  have eq15591 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq8211 X0 X1
       grind)
    | exact superpose eq8211 eq10
    | (have j1 := eq8211 X0 X1
       grind)
    | exact resolve eq10 eq8211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8211
  have eq15691 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15591 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq15591
    | (have j0 := eq15591 X0 X1
       grind)
    | exact resolve eq15591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15591
  have eq15712 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15691 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq15691 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq15691 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq15691 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15691
  have eq16032 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1490
       have i₂ := eq15712 x y
       grind)
    | exact superpose eq15712 eq1490
    | (have j1 := eq15712 x y
       grind)
    | exact resolve eq1490 eq15712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq16034 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15712 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15712
  have eq16036 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16032
  have eq16273 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1509 x y
       have i₂ := eq16036
       grind)
    | exact superpose eq16036 eq1509
    | (have j0 := eq1509 x y
       grind)
    | exact resolve eq1509 eq16036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509 eq16036
  have eq16294 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16273
  have eq16295 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16294
  have eq16311 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16295
       grind)
    | exact superpose eq16295 eq16
    | exact resolve eq16 eq16295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16316 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16034 (σ x) (σ y)
       have i₂ := eq16295
       grind)
    | exact superpose eq16295 eq16034
    | (have j0 := eq16034 (σ x) (σ y)
       grind)
    | (have r₁ := eq16034 (σ x) (σ y)
       have r₂ := eq16295
       grind)
    | exact resolve eq16034 eq16295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16034 eq16295
  have eq16317 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq16316
  have eq16320 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16317
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16317
    | exact resolve eq16317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16317
  have eq16443 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq859 y x
       have i₂ := eq16320
       grind)
    | exact superpose eq16320 eq859
    | (have j0 := eq859 y x
       grind)
    | exact resolve eq859 eq16320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq16320
  have eq16567 : x = (M.op x y) := by
    first
    | (have r₁ := eq16443
       have r₂ := eq16311
       grind)
    | exact resolve eq16443 eq16311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16443
  have eq16707 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq16311
       have i₂ := eq16567
       grind)
    | exact superpose eq16567 eq16311
    | exact resolve eq16311 eq16567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16311 eq16567
  have eq16719 : False := by grind
  exact eq16719

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_x_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq395 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq412 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq395
    | (have j0 := eq395 X0 X1
       grind)
    | exact resolve eq395 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq692 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq412 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq412
    | exact resolve eq412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq719 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq692
    | (have j0 := eq692 X0 X1
       grind)
    | exact resolve eq692 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq692
  have eq722 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq719 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq719 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq719 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq719 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq719
  have eq724 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq722
    | exact resolve eq722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq722 (σ X0) X1
       grind)
    | exact superpose eq722 eq15
    | (have j1 := eq722 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq771 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq724 (τ X1) X0
       grind)
    | exact superpose eq724 eq19
    | (have j1 := eq724 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq724
  have eq874 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq771 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq771
    | exact resolve eq771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq924 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq874 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq874
    | (have j0 := eq874 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq874 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq1087 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq738 x y
       grind)
    | exact superpose eq738 eq16
    | (have j1 := eq738 x y
       grind)
    | exact resolve eq16 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq1103 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1087
       have i₂ := eq924 y x
       grind)
    | exact superpose eq924 eq1087
    | (have j1 := eq924 (σ x) (σ y)
       grind)
    | (have r₁ := eq1087
       have r₂ := eq924 y x
       grind)
    | (have r₁ := eq1087
       have r₂ := eq924 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1087
       have r₂ := eq924 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1087 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924 eq1087
  have eq1104 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1103
  have eq1107 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1104
       grind)
    | exact superpose eq1104 eq16
    | exact resolve eq16 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1108 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1107
       have r₂ := eq76 x
       grind)
    | exact resolve eq1107 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1109 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1108
       grind)
    | exact superpose eq1108 eq16
    | exact resolve eq16 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1108
       grind)
    | exact superpose eq1108 eq10
    | exact resolve eq10 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1156 : x = y := by
    first
    | (have i₁ := eq1110
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1110
    | exact resolve eq1110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1157 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1109
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq1109
    | exact resolve eq1109 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1109
  have eq1158 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1157
       have i₂ := eq1156
       grind)
    | exact superpose eq1156 eq1157
    | exact resolve eq1157 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156 eq1157
  have eq1159 : False := by grind
  exact eq1159

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
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
  have eq766 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq3647 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq782 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq12493 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq766 X0 X1
       grind)
    | exact superpose eq766 eq12
    | (have j1 := eq766 X1 X0
       grind)
    | (have r₁ := eq12 X1 (σ X0)
       have r₂ := eq766 X0 X1
       grind)
    | exact resolve eq12 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq12495 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12493 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12493
  have eq25789 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12495 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12495
    | exact resolve eq12495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12495
  have eq25913 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25789 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq25789
    | (have j0 := eq25789 X0 X1
       grind)
    | exact resolve eq25789 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25789
  have eq25944 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X0 X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25913 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq25913
    | (have j0 := eq25913 (τ X0) (τ X1)
       grind)
    | exact resolve eq25913 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25913
  have eq27205 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3647 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq3647
    | (have j0 := eq3647 (τ X1) (τ X0)
       grind)
    | exact resolve eq3647 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27345 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27205 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq27205
    | (have j0 := eq27205 X0 X1
       grind)
    | exact resolve eq27205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27205
  have eq27413 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27345 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27345
    | (have j0 := eq27345 X0 X1
       grind)
    | exact resolve eq27345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27345
  have eq27471 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27413 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27413
    | (have j0 := eq27413 X0 X1
       grind)
    | exact resolve eq27413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27413
  have eq27505 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27471 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27471
    | (have j0 := eq27471 X0 X1
       grind)
    | exact resolve eq27471 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27471
  have eq27529 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27505 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27505
    | (have j0 := eq27505 X0 X1
       grind)
    | exact resolve eq27505 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27505
  have eq27545 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27529 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27529
    | (have j0 := eq27529 X0 X1
       grind)
    | exact resolve eq27529 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27529
  have eq709080 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq25944 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq25944 X0 X1
       grind)
    | exact superpose eq25944 eq13
    | (have j0 := eq13 (τ X1) (τ X0)
       have j1 := eq25944 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq25944 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq25944 X0 X1
       grind)
    | exact resolve eq13 eq25944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25944
  have eq709081 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq709080 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709080
  have eq709085 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq709081 X0 X1
       have j1 := eq12 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq709081 X0 X1
       have r₂ := eq12 (τ X1) (τ X0)
       grind)
    | exact resolve eq709081 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709081
  have eq709175 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq709085 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq709085
    | (have j0 := eq709085 X0 X1
       grind)
    | exact resolve eq709085 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq709085
  have eq709360 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op (τ X1) X0)) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq709175 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq709175
    | exact resolve eq709175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709175
  have eq709940 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op (τ X1) X0)) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq709360 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq709360
    | (have j0 := eq709360 X0 X1
       grind)
    | exact resolve eq709360 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709360
  have eq710047 : ∀ X0 X1 : G, (τ (k X0 (τ X1))) = (τ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq709940 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq709940
    | (have j0 := eq709940 X0 X1
       grind)
    | exact resolve eq709940 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709940
  have eq710129 : ∀ X0 X1 : G, (τ (k X0 (τ X1))) = (τ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq710047 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq710047
    | (have j0 := eq710047 X0 X1
       grind)
    | exact resolve eq710047 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710047
  have eq711659 : ∀ X0 X1 : G, (k X1 (τ X0)) = (σ (τ (M.op (τ X0) X1))) ∨ (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 (τ X0))
       have i₂ := eq710129 X1 X0
       grind)
    | exact superpose eq710129 eq11
    | (have j1 := eq710129 X1 X0
       grind)
    | exact resolve eq11 eq710129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710129
  have eq713554 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq711659 X0 X1
       have i₂ := eq11 (M.op (τ X0) X1)
       grind)
    | exact superpose eq11 eq711659
    | (have j0 := eq711659 X0 X1
       grind)
    | exact resolve eq711659 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711659
  have eq713555 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq713554 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713554
  have eq713596 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq713555 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq713555
    | exact resolve eq713555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713730 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq713555 X0 X1
       grind)
    | exact superpose eq713555 eq18
    | (have j1 := eq713555 X0 X1
       grind)
    | exact resolve eq18 eq713555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq713555
  have eq715749 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq713596 (σ X0) X1
       grind)
    | exact superpose eq713596 eq22
    | (have j1 := eq713596 (σ X0) X1
       grind)
    | exact resolve eq22 eq713596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq713596
  have eq717919 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq713730 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq713730
    | exact resolve eq713730 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713730
  have eq718365 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq717919 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq717919
    | (have j0 := eq717919 X0 X1
       grind)
    | exact resolve eq717919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717919
  have eq719939 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq715749 X1 (σ X0)
       grind)
    | exact superpose eq715749 eq28
    | (have j1 := eq715749 X1 (σ X0)
       grind)
    | exact resolve eq28 eq715749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq715749
  have eq720797 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq719939 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq719939
    | (have j0 := eq719939 X0 X1
       grind)
    | exact resolve eq719939 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719939
  have eq721211 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq720797 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq720797
    | (have j0 := eq720797 X0 X1
       grind)
    | exact resolve eq720797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720797
  have eq721279 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq721211 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq721211
    | (have j0 := eq721211 X0 X1
       grind)
    | exact resolve eq721211 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721211
  have eq724086 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq721279 X0 X1
       grind)
    | exact superpose eq721279 eq11
    | (have j1 := eq721279 X0 X1
       grind)
    | exact resolve eq11 eq721279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721279
  have eq725850 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq724086 y x
       grind)
    | exact superpose eq724086 eq16
    | (have j1 := eq724086 y x
       grind)
    | exact resolve eq16 eq724086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724086
  have eq726290 : y = (k y x) := by
    first
    | (have j1 := eq718365 x y
       grind)
    | (have r₁ := eq725850
       have r₂ := eq718365 x y
       grind)
    | exact resolve eq725850 eq718365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718365 eq725850
  have eq726642 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3647 x y
       have i₂ := eq726290
       grind)
    | exact superpose eq726290 eq3647
    | (have j0 := eq3647 y x
       grind)
    | exact resolve eq3647 eq726290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3647
  have eq726676 : y ≠ y ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27545 y x
       have i₂ := eq726290
       grind)
    | exact superpose eq726290 eq27545
    | (have j0 := eq27545 y x
       grind)
    | (have r₁ := eq27545 y x
       have r₂ := eq726290
       grind)
    | exact resolve eq27545 eq726290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27545
  have eq726702 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq726676
  have eq726704 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq726642
  have eq726730 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq726702
       grind)
    | exact superpose eq726702 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq726702
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq726702
       grind)
    | exact resolve eq13 eq726702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726702
  have eq726732 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq726730
  have eq726733 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq726732
  have eq726735 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq726733
       have r₂ := eq12 y x
       grind)
    | exact resolve eq726733 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726733
  have eq726757 : y = (M.op x y) := by
    first
    | (have i₁ := eq726735
       have i₂ := eq726290
       grind)
    | exact superpose eq726290 eq726735
    | exact resolve eq726735 eq726290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726735
  have eq902856 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq726704
       grind)
    | exact superpose eq726704 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq726704
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq726704
       grind)
    | exact resolve eq13 eq726704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726704
  have eq902859 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq902856
  have eq902860 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq902859
  have eq902865 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq902860
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq902860 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902860
  have eq902895 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq902865
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq902865
    | exact resolve eq902865 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902865
  have eq902900 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq902895
       have i₂ := eq726290
       grind)
    | exact superpose eq726290 eq902895
    | exact resolve eq902895 eq726290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726290 eq902895
  have eq902907 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq902900
       grind)
    | exact superpose eq902900 eq16
    | exact resolve eq16 eq902900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902900
  have eq903029 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq902907
       have i₂ := eq726757
       grind)
    | exact superpose eq726757 eq902907
    | exact resolve eq902907 eq726757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726757 eq902907
  have eq903030 : False := by grind
  exact eq903030
