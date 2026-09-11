import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq69 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq70 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq71 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq88 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq88 y x
       grind)
    | exact superpose eq88 eq67
    | (have j1 := eq88 y x
       grind)
    | exact resolve eq67 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq88 sF3 sF2
       grind)
    | exact superpose eq88 eq77
    | (have j1 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq77 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq110 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq107
    | exact resolve eq107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq112 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq110
    | exact resolve eq110 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq117
    | exact resolve eq117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq118
       have r₂ := eq27
       grind)
    | exact resolve eq118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq123 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq123 eq27
    | exact resolve eq27 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq67
    | exact resolve eq67 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq427 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq424
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq424
    | exact resolve eq424 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq475 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq123 eq71
    | (have r₁ := eq71
       have r₂ := eq123
       grind)
    | exact resolve eq71 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq123
  have eq476 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq475
  have eq481 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq476 eq114
    | exact resolve eq114 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq485 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq481
  have eq492 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq485
       have r₂ := eq125
       grind)
    | exact resolve eq485 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq485
  have eq497 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq492 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq492
       grind)
    | exact resolve eq13 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq499 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq497 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq531 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq50 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq50 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq499 eq114
    | exact resolve eq114 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq499
  have eq560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq557
  have eq565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq560
    | exact resolve eq560 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq560
  have eq567 : x = (M.op x y) := by
    first
    | (have r₁ := eq565
       have r₂ := eq27
       grind)
    | exact resolve eq565 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq569 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq567 eq20
    | exact resolve eq20 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq567 eq70
    | (have r₁ := eq70
       have r₂ := eq567
       grind)
    | exact resolve eq70 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq578 : x = (M.op x x) ∨ x = (k y x) := by grind
  clear eq572
  have eq586 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq569
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq569
    | exact resolve eq569 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq672 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq586 eq427
    | exact resolve eq427 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq677 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq672
       have r₂ := eq27
       grind)
    | exact resolve eq672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq688 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq677 eq87
    | exact resolve eq87 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq690 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq567 eq688
    | exact resolve eq688 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq853 : x = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq578
       have i₂ := eq690
       grind)
    | exact superpose eq690 eq578
    | exact resolve eq578 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq690
  have eq1110 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq531 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq531
    | (have j0 := eq531 x y X0
       grind)
    | exact resolve eq531 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1147 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x x)) := by
    intro X0
    first
    | exact superpose eq567 eq1110
    | exact resolve eq1110 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1169 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq1147 (M.op x x)
       have i₂ := eq1147 x
       grind)
    | exact superpose eq1147 eq1147
    | exact resolve eq1147 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq531 X0 X1 (M.op x x)
       have i₂ := eq1147 x
       grind)
    | exact superpose eq1147 eq531
    | exact resolve eq531 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq1147
  have eq1486 : x = (M.op y (M.op x x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1188 x x
       have i₂ := eq853
       grind)
    | exact superpose eq853 eq1188
    | exact resolve eq1188 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq1188
  have eq1521 : x = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq1486
       have i₂ := eq1169
       grind)
    | exact superpose eq1169 eq1486
    | exact resolve eq1486 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq1486
  have eq1537 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1521 eq15
    | exact resolve eq15 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1555 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1537
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1537
    | exact resolve eq1537 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1537
  have eq1560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq586 eq1555
    | exact resolve eq1555 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq1564 : x = y := by
    first
    | (have r₁ := eq1560
       have r₂ := eq27
       grind)
    | exact resolve eq1560 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq1565 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1564
       grind)
    | exact superpose eq1564 eq18
    | exact resolve eq18 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1595 : x = (M.op x x) := by
    first
    | exact superpose eq567 eq1565
    | exact resolve eq1565 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq1565
  have eq1649 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1595
       grind)
    | exact superpose eq1595 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1595
       grind)
    | exact resolve eq13 eq1595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1663 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1649 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq1962 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq1663 y
       grind)
    | exact superpose eq1663 eq67
    | exact resolve eq67 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1663
  have eq1974 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq586 eq1962
    | exact resolve eq1962 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq1962
  have eq1987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq677 eq1974
    | exact resolve eq1974 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq1974
  have eq1996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1987
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1987
    | exact resolve eq1987 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1987
  have eq2002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1996
    | exact resolve eq1996 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1996
  have eq2007 : False := by grind
  exact eq2007

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pxy_pyx_Equation731 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq92 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) X3 X2
       have i₂ := eq9 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1683 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 (M.op X1 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X2 X2) x
       have i₂ := eq92 x X3 X2 X1
       grind)
    | (have i₁ := eq9 X1 (M.op X2 X2) X2
       have i₂ := eq92 x X1 X2 (M.op X2 X2)
       grind)
    | exact superpose eq92 eq9
    | exact resolve eq9 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq2096 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X0))) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1683 X0 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq1683 X0 X2 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq1683
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq1683 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2207 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2096 X0 X1 x
       have i₂ := eq1683 X0 x X0
       grind)
    | (have i₁ := eq2096 X0 X1 x
       have i₂ := eq1683 X1 x (M.op (M.op x x) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq1683 eq2096
    | (have j0 := eq2096 X0 X1 x
       grind)
    | exact resolve eq2096 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683 eq2096
  have eq2208 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq2211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2208 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2208
    | (have j0 := eq2208 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq2208 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2214 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq2208 X0 (τ X1)
       grind)
    | exact superpose eq2208 eq19
    | (have j1 := eq2208 (k (σ X0) X1) (σ (M.op (τ X1) X0))
       grind)
    | exact resolve eq19 eq2208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2208
  have eq3274 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2214 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2214
    | exact resolve eq2214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq3321 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3274 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3274
    | (have j0 := eq3274 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq3274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq14879 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2211 y x
       grind)
    | exact superpose eq2211 eq16
    | (have j1 := eq2211 x y
       grind)
    | exact resolve eq16 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq14939 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14879
       have i₂ := eq3321 x y
       grind)
    | exact superpose eq3321 eq14879
    | (have j1 := eq3321 (σ x) (σ y)
       grind)
    | (have r₁ := eq14879
       have r₂ := eq3321 x y
       grind)
    | (have r₁ := eq14879
       have r₂ := eq3321 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq14879
       have r₂ := eq3321 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq14879 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321 eq14879
  have eq14940 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq14939
  have eq14944 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14940
       grind)
    | exact superpose eq14940 eq10
    | exact resolve eq10 eq14940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14940
  have eq14986 : x = y ∨ x = y := by
    first
    | (have i₁ := eq14944
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14944
    | exact resolve eq14944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14944
  have eq14987 : x = y := by grind
  clear eq14986
  have eq14989 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14987
       grind)
    | exact superpose eq14987 eq16
    | exact resolve eq16 eq14987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14987
  have eq14990 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14989
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq14989
    | (have r₁ := eq14989
       have r₂ := eq22 x
       grind)
    | exact resolve eq14989 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14989
  have eq14991 : False := by grind
  exact eq14991

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyx_pxy_Equation731 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq34
  have eq46 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq97 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq270 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X3 (M.op X1 X1) X2
       have i₂ := eq64 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq64 X3 (M.op X1 X1) X2
       have i₂ := eq64 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2 (M.op X1 X1)
       have i₂ := eq64 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq9 X3 X2 (M.op X1 X1)
       have i₂ := eq64 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X1) X2
       have i₂ := eq64 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X0 X1
       grind)
    | (have i₁ := eq9 X3 (M.op X1 X1) X2
       have i₂ := eq64 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X1 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq50 eq294
    | exact resolve eq294 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq323 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq50
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq327 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq323
    | exact resolve eq323 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq329 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq327
    | exact resolve eq327 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq331 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq329
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq329
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq329 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq331
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq331
    | exact resolve eq331 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq341
    | exact resolve eq341 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq343 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq342
       have r₂ := eq28
       grind)
    | exact resolve eq342 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq344 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq343
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq343
    | exact resolve eq343 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq704 : (σ x) ≠ (σ x) ∨ (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq344 eq295
    | (have r₁ := eq295
       have r₂ := eq344
       grind)
    | exact resolve eq295 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq705 : (σ x) ≠ (σ x) ∨ (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq704
  have eq706 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq705
  have eq707 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq706
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq706
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq706 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq721 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq707
  have eq722 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq721
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq721
    | exact resolve eq721 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq723 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq722
    | exact resolve eq722 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq724 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq723
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq723
    | exact resolve eq723 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq725 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq724
  have eq750 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq63 X1 X4 x x
       have i₂ := eq63 X1 X0 x x
       grind)
    | (have i₁ := eq63 X0 X1 x x
       have i₂ := eq63 X0 (M.op x x) x x
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2))) = (M.op X5 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq63 (M.op X5 X2) X5 X3 X4
       have i₂ := eq63 X2 X5 X0 X1
       grind)
    | (have i₁ := eq63 (M.op (M.op X3 X3) X0) (M.op X2 X2) X2 X3
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq63 X1 X0 x X4
       grind)
    | (have i₁ := eq9 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq63 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq63 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq63 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X3 (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have i₂ := eq63 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq63 eq64
    | exact resolve eq64 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1211 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X3 X3) X0)))) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq750 X1 (M.op X2 (M.op (M.op X3 X3) X0)) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq750
    | exact resolve eq750 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq750 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq750
    | (have j0 := eq750 X0 y x
       grind)
    | exact resolve eq750 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : ∀ X0 : G, (M.op (σ y) (σ (M.op x y))) = (M.op X0 (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq725 eq750
    | exact resolve eq750 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq1631 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 X2) (M.op X3 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq768 X3 (M.op X3 X1) X2
       have i₂ := eq750 X3 X1 X0
       grind)
    | (have i₁ := eq768 X3 (M.op X3 X1) X2
       have i₂ := eq750 X0 X1 X3
       grind)
    | exact superpose eq750 eq768
    | exact resolve eq768 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq1633 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op (M.op X0 X0) (M.op X1 (M.op (σ y) (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1220 eq768
    | exact resolve eq768 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq6924 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) X1) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1633 eq64
    | exact resolve eq64 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq6926 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) (M.op X0 (M.op X0 X1))) = X1 ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f6926_15 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
      intro X0 X1 X2
      grind
    have f6926_16 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op (M.op X0 X0) (M.op X1 (M.op (σ y) (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0 X1
      grind
    have f6926_17 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f6926_25 : X1 ≠ (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) (M.op X0 (M.op X0 X1))) := by grind
    have f6926_26 : x ≠ (M.op x y) := by grind
    have f6926_27 : (σ x) ≠ (σ y) := by grind
    have f6926_28 : x ≠ y := by grind
    have f6926_30 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op (M.op X0 X0) (M.op X1 (M.op (σ y) (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0 X1
      first
      | (have j0 := f6926_16 X0 X1
         grind)
      | (have r₁ := f6926_16 X0 X1
         have r₂ := f6926_26
         grind)
      | exact resolve f6926_16 f6926_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6926_31 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op (M.op X0 X0) (M.op X1 (M.op (σ y) (σ (M.op x y))))) ∨ x = y := by
      intro X0 X1
      first
      | (have j0 := f6926_30 X0 X1
         grind)
      | (have r₁ := f6926_30 X0 X1
         have r₂ := f6926_27
         grind)
      | exact resolve f6926_30 f6926_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6926_32 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op (M.op X0 X0) (M.op X1 (M.op (σ y) (σ (M.op x y))))) := by
      intro X0 X1
      first
      | (have j0 := f6926_31 X0 X1
         grind)
      | (have r₁ := f6926_31 X0 X1
         have r₂ := f6926_28
         grind)
      | exact resolve f6926_31 f6926_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6926_59 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op X1 (M.op X1 X0)) := by
      intro X0 X1 X3
      first
      | (have i₁ := f6926_17 (M.op X1 (M.op X1 X0)) X3 x
         have i₂ := f6926_15 X1 X0 x
         grind)
      | exact superpose f6926_15 f6926_17
      | exact resolve f6926_17 f6926_15
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6926_129 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) (M.op X0 (M.op X0 X1))) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f6926_15 X0 X1 (M.op (M.op (σ y) (σ (M.op x y))) (M.op (σ y) (σ (M.op x y))))
         have i₂ := f6926_32 (M.op (σ y) (σ (M.op x y))) (M.op (σ y) (σ (M.op x y)))
         grind)
      | exact superpose f6926_32 f6926_15
      | exact resolve f6926_15 f6926_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6926_251 : ∀ X0 : G, X1 ≠ (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) (M.op X0 (M.op X0 X1))) := by
      intro X0
      first
      | (have i₁ := f6926_25
         have i₂ := f6926_59 X1 X0 X0
         grind)
      | (have i₁ := f6926_25
         have i₂ := f6926_59 X1 X0 X0
         grind)
      | exact superpose f6926_59 f6926_25
      | exact resolve f6926_25 f6926_59
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6926_252 : False := by
      first
      | (have r₁ := f6926_251 x
         have r₂ := f6926_129 x X1
         grind)
      | exact resolve f6926_251 f6926_129
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f6926_252
  clear eq1633
  have eq9014 : (σ y) = (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq6926
    | (have j0 := eq6926 (σ x) (σ y)
       grind)
    | exact resolve eq6926 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6926
  have eq9146 : (σ y) = (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq344 eq9014
    | exact resolve eq9014 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq9014
  have eq9160 : (σ y) = (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9146
  have eq9165 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9160 eq6924
    | exact resolve eq6924 eq9160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6924 eq9160
  have eq9179 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq9165 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9165
  have eq9947 : (τ (σ y)) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9179 eq161
    | exact resolve eq161 eq9179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9179
  have eq9992 : (τ (σ y)) = (M.op (M.op (τ (σ x)) (τ (σ x))) (M.op (τ (σ x)) (τ (σ x)))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9947
       have i₂ := eq161 sF2
       grind)
    | exact superpose eq161 eq9947
    | exact resolve eq9947 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq9947
  have eq9995 : (τ (σ y)) = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq46 eq9992
    | exact resolve eq9992 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9992
  have eq9997 : y = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq47 eq9995
    | exact resolve eq9995 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9995
  have eq10671 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 (M.op x x) X0 x
       have i₂ := eq9997
       grind)
    | exact superpose eq9997 eq9
    | exact resolve eq9 eq9997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9997
  have eq13382 : ∀ X0 X1 : G, x = (M.op (M.op X1 X1) (M.op x (M.op X0 (M.op X0 y)))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq768 x x X1
       have i₂ := eq10671 X0
       grind)
    | exact superpose eq10671 eq768
    | exact resolve eq768 eq10671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10671
  have eq13457 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13382 x x
       have i₂ := eq1631 x y x x
       grind)
    | exact superpose eq1631 eq13382
    | exact resolve eq13382 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631 eq13382
  have eq13461 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13457
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13457
    | exact resolve eq13457 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13457
  have eq13462 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13461
  have eq14218 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13462 eq47
    | exact resolve eq47 eq13462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq13462
  have eq14231 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq46 eq14218
    | exact resolve eq14218 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq14218
  have eq14232 : x = (M.op x y) ∨ x = y := by grind
  clear eq14231
  have eq14236 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14232 eq21
    | exact resolve eq21 eq14232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14243 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14236
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14236
    | exact resolve eq14236 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14236
  have eq36286 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X4 X4) (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3))) = (M.op X7 (M.op X7 (M.op X2 (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq767 X2 (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3)) X7 X4
       have i₂ := eq756 X5 X6 X3 X0 X1 X2
       grind)
    | (have i₁ := eq767 (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2)) X2 X4
       have i₂ := eq756 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq756 eq767
    | exact resolve eq767 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq767
  have eq36372 : ∀ X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 X4) (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3))) = (M.op X2 (M.op (M.op X1 X1) (M.op X2 X3))) := by
    intro X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq36286 x X1 X2 X3 X4 X5 X6 x
       have i₂ := eq1211 (M.op (M.op X1 X1) (M.op X2 X3)) x X2 x
       grind)
    | exact superpose eq1211 eq36286
    | exact resolve eq36286 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211 eq36286
  have eq36585 : ∀ X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X1) (M.op X2 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq36372 X1 X2 X3 x x x
       have i₂ := eq285 x x x X3
       grind)
    | exact superpose eq285 eq36372
    | exact resolve eq36372 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36372
  have eq64707 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14232 eq1218
    | exact resolve eq1218 eq14232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14232
  have eq64726 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (M.op x (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq773 y y X0 X1
       have i₂ := eq1218 y
       grind)
    | exact superpose eq1218 eq773
    | exact resolve eq773 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq65729 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (M.op (M.op (M.op X3 X3) (M.op X0 (M.op X0 y))) X2) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq270 X3 x X1 X2
       have i₂ := eq64707 X0
       grind)
    | exact superpose eq64707 eq270
    | exact resolve eq270 eq64707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq65731 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op (M.op (M.op X2 X2) (M.op X0 (M.op X0 y))) X3))) = X3 ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq283 X2 x X1 X3
       have i₂ := eq64707 X0
       grind)
    | exact superpose eq64707 eq283
    | exact resolve eq283 eq64707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq65838 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq285 X0 x x y
       have i₂ := eq64707 (M.op x x)
       grind)
    | exact superpose eq64707 eq285
    | exact resolve eq285 eq64707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq64707
  have eq65956 : ∀ X1 X3 : G, (M.op X1 (M.op X1 (M.op y X3))) = X3 ∨ x = y := by
    intro X1 X3
    first
    | (have i₁ := eq65731 x X1 x X3
       have i₂ := eq768 x y x
       grind)
    | exact superpose eq768 eq65731
    | exact resolve eq65731 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65731
  have eq65957 : ∀ X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op y X2) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq65729 x X1 X2 x
       have i₂ := eq768 x y x
       grind)
    | exact superpose eq768 eq65729
    | exact resolve eq65729 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq65729
  have eq66325 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ x = y := by
    first
    | (have i₁ := eq35 (M.op x x)
       have i₂ := eq65838 x
       grind)
    | exact superpose eq65838 eq35
    | exact resolve eq35 eq65838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65838
  have eq66469 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq66325
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq66325
    | exact resolve eq66325 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66325
  have eq66478 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq66469
       have i₂ := eq64726 (σ x) (M.op (σ x) (σ x))
       grind)
    | exact superpose eq64726 eq66469
    | exact resolve eq66469 eq64726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64726 eq66469
  have eq66481 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq66478
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq66478
    | exact resolve eq66478 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66478
  have eq66484 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq66481
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq66481
    | exact resolve eq66481 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66481
  have eq66575 : y = (M.op y (M.op x (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq65956 y y
       have i₂ := eq1218 y
       grind)
    | exact superpose eq1218 eq65956
    | exact resolve eq65956 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218 eq65956
  have eq73011 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X0 X1))) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq36585 x X0 X1
       have i₂ := eq65957 x (M.op X0 X1)
       grind)
    | exact superpose eq65957 eq36585
    | exact resolve eq36585 eq65957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36585 eq65957
  have eq94765 : (σ y) = (M.op y (M.op (σ x) (σ x))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq66575 eq66484
    | exact resolve eq66484 eq66575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66484 eq66575
  have eq94809 : (σ y) = (M.op y (M.op (σ x) (σ x))) ∨ x = y := by grind
  clear eq94765
  have eq94827 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq94809 eq73011
    | exact resolve eq73011 eq94809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73011 eq94809
  have eq94860 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq94827
  have eq94868 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq94860
    | exact resolve eq94860 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94860
  have eq94874 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq94868 eq28
    | exact resolve eq28 eq94868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94868
  have eq94958 : x = y := by
    first
    | (have r₁ := eq94874
       have r₂ := eq14243
       grind)
    | exact resolve eq94874 eq14243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14243 eq94874
  have eq94959 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq94958
       grind)
    | exact superpose eq94958 eq19
    | exact resolve eq19 eq94958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq94960 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq94958
       grind)
    | exact superpose eq94958 eq25
    | exact resolve eq25 eq94958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq94958
  have eq96931 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq94960
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq94960
    | exact resolve eq94960 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94960
  have eq97442 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq96931 eq27
    | exact resolve eq27 eq96931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq96931
  have eq99991 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq94959
       grind)
    | exact superpose eq94959 eq35
    | exact resolve eq35 eq94959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq94959
  have eq100956 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq99991
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq99991
    | exact resolve eq99991 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq99991
  have eq101887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq97442 eq100956
    | exact resolve eq100956 eq97442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97442 eq100956
  have eq102668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq101887
    | exact resolve eq101887 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq101887
  have eq103157 : False := by grind
  exact eq103157

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pyx_Equation731 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq44 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq147 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq24 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq24 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq276 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq44
    | (have j0 := eq44 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq751 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq147 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq147
    | exact resolve eq147 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28415 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq276 x y
       grind)
    | exact superpose eq276 eq16
    | (have j1 := eq276 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq276 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq276 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq276 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq28530 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq28415
  have eq103388 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq147 (σ x) (σ y) X0
       have i₂ := eq28530
       grind)
    | exact superpose eq28530 eq147
    | exact resolve eq147 eq28530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28530
  have eq103527 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq103388 x
       have i₂ := eq751 x x
       grind)
    | exact superpose eq751 eq103388
    | exact resolve eq103388 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq103388
  have eq103528 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq103527
  have eq106232 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq147 x y X0
       have i₂ := eq103528
       grind)
    | exact superpose eq103528 eq147
    | exact resolve eq147 eq103528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103528
  have eq106360 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq106232 x
       have i₂ := eq147 x x x
       grind)
    | exact superpose eq147 eq106232
    | exact resolve eq106232 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq106232
  have eq106361 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq106360
  have eq113994 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq106361
       grind)
    | exact superpose eq106361 eq10
    | exact resolve eq10 eq106361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106361
  have eq114097 : x = y ∨ x = y := by
    first
    | (have i₁ := eq113994
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq113994
    | exact resolve eq113994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113994
  have eq114098 : x = y := by grind
  clear eq114097
  have eq126540 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114098
       grind)
    | exact superpose eq114098 eq16
    | exact resolve eq16 eq114098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114098
  have eq126541 : False := by grind
  exact eq126541

/-- `Equation826`: `x = x ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation826 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law826 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law826.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 x y
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : (k y y) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq565
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq565
    | exact resolve eq565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq1225 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 y x
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq1225
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1225
    | exact resolve eq1225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1243 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1235
       have i₂ := eq21 (σ y) (σ x)
       grind)
    | exact superpose eq21 eq1235
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1235
       have r₂ := eq21 (σ y) (σ x)
       grind)
    | (have r₁ := eq1235
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1235
       have r₂ := eq21 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1235 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1235
  have eq1245 : x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1243
  have eq1321 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1245
       grind)
    | exact superpose eq1245 eq9
    | exact resolve eq9 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq1322 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1321
  have eq1323 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1322
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1322
    | exact resolve eq1322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1324 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1323
  have eq1325 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1324
  have eq1403 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1325
       grind)
    | exact superpose eq1325 eq10
    | exact resolve eq10 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1405 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1403
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1403
    | exact resolve eq1403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq1406 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1405
  have eq1409 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1406
       grind)
    | exact superpose eq1406 eq22
    | exact resolve eq22 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1456 : (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1409
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1409
    | exact resolve eq1409 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1409
  have eq1478 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq572
       have i₂ := eq1456
       grind)
    | exact superpose eq1456 eq572
    | (have r₁ := eq572
       have r₂ := eq1456
       grind)
    | exact resolve eq572 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1456
  have eq1481 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1478
  have eq1485 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1481
       have i₂ := eq20 (σ x) (σ y)
       grind)
    | exact superpose eq20 eq1481
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1481
       have r₂ := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1481
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1481
       have r₂ := eq20 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1481 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1481
  have eq1486 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1485
  have eq1487 : x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1486
  have eq1489 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1487
       have r₂ := eq1406
       grind)
    | exact resolve eq1487 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406 eq1487
  have eq1490 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1489
       grind)
    | exact superpose eq1489 eq9
    | exact resolve eq9 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1491 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1490
  have eq1492 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1491
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1491
    | exact resolve eq1491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1493 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1492
  have eq1494 : (σ x) = (σ y) := by grind
  clear eq1493
  have eq1496 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1494
       grind)
    | exact superpose eq1494 eq15
    | exact resolve eq15 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq1543 : x = y := by
    first
    | (have i₁ := eq1496
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1496
    | exact resolve eq1496 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1546 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1543
       grind)
    | exact superpose eq1543 eq9
    | exact resolve eq9 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1547 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1546
  have eq1548 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1547
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1547
    | exact resolve eq1547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq1549 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1548
  have eq1550 : False := by grind
  exact eq1550

/-- `Equation826`: `x = x ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation826 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law826 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law826.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq98 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq252 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq16
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq726 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq763 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq726
    | (have j0 := eq726 X0 X1
       grind)
    | exact resolve eq726 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq832 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 (τ X1) (τ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq259
    | (have j0 := eq259 (τ X1) (τ X0)
       grind)
    | exact resolve eq259 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq840 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq832 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq832
    | (have j0 := eq832 X0 X1
       grind)
    | exact resolve eq832 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq843 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq840 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq840
    | (have j0 := eq840 X0 X1
       grind)
    | exact resolve eq840 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq845 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq843
    | (have j0 := eq843 X0 X1
       grind)
    | exact resolve eq843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq846 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq845
    | (have j0 := eq845 X0 X1
       grind)
    | exact resolve eq845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq847 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq846 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq846
    | (have j0 := eq846 X0 X1
       grind)
    | exact resolve eq846 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq848 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq847 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq847
    | (have j0 := eq847 X0 X1
       grind)
    | exact resolve eq847 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq1014 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq252
       have i₂ := eq763 y x
       grind)
    | exact superpose eq763 eq252
    | (have j1 := eq763 (σ y) (σ x)
       grind)
    | (have r₁ := eq252
       have r₂ := eq763 y x
       grind)
    | (have r₁ := eq252
       have r₂ := eq763 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq252
       have r₂ := eq763 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq252 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq763
  have eq1015 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1014
  have eq16910 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq16
    | exact resolve eq16 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq16911 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16910
       have r₂ := eq22 x
       grind)
    | exact resolve eq16910 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16910
  have eq16913 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16911
       grind)
    | exact superpose eq16911 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16911
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq16911
       grind)
    | exact resolve eq13 eq16911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16911
  have eq16922 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16913
  have eq20929 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16922
       grind)
    | exact superpose eq16922 eq16
    | exact resolve eq16 eq16922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16922
  have eq20930 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20929
       have r₂ := eq22 x
       grind)
    | exact resolve eq20929 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20929
  have eq21211 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq259 x y
       have i₂ := eq20930
       grind)
    | exact superpose eq20930 eq259
    | (have j0 := eq259 x y
       grind)
    | exact resolve eq259 eq20930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq20930
  have eq21236 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq21211
  have eq21237 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq21236
  have eq21243 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21237
       grind)
    | exact superpose eq21237 eq16
    | exact resolve eq16 eq21237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21250 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq21237
       grind)
    | exact superpose eq21237 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21237
       grind)
    | exact resolve eq13 eq21237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21237
  have eq21262 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq21250
  have eq21263 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq21262
  have eq21276 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq21263
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq21263
    | exact resolve eq21263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21263
  have eq21554 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21276
       grind)
    | exact superpose eq21276 eq10
    | exact resolve eq10 eq21276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21276
  have eq21651 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq21554
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21554
    | exact resolve eq21554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21554
  have eq22021 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21651
       grind)
    | exact superpose eq21651 eq16
    | exact resolve eq16 eq21651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21651
  have eq22022 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq22021
       have r₂ := eq22 x
       grind)
    | exact resolve eq22021 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22021
  have eq22037 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq22022
       grind)
    | exact superpose eq22022 eq10
    | exact resolve eq10 eq22022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22022
  have eq22137 : x = (k y x) := by
    first
    | (have i₁ := eq22037
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22037
    | exact resolve eq22037 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22037
  have eq22168 : x ≠ x ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq848 y x
       have i₂ := eq22137
       grind)
    | exact superpose eq22137 eq848
    | (have j0 := eq848 y x
       grind)
    | (have r₁ := eq848 y x
       have r₂ := eq22137
       grind)
    | exact resolve eq848 eq22137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq22137
  have eq22186 : x = y ∨ x = (M.op x y) := by grind
  clear eq22168
  have eq22191 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22186
       grind)
    | exact superpose eq22186 eq16
    | exact resolve eq16 eq22186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22186
  have eq22196 : x = (M.op x y) := by
    first
    | (have r₁ := eq22191
       have r₂ := eq22 x
       grind)
    | exact resolve eq22191 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22191
  have eq22394 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq21243
       have i₂ := eq22196
       grind)
    | exact superpose eq22196 eq21243
    | exact resolve eq21243 eq22196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21243 eq22196
  have eq22409 : (σ x) = (σ y) := by grind
  clear eq22394
  have eq22411 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22409
       grind)
    | exact superpose eq22409 eq10
    | exact resolve eq10 eq22409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22409
  have eq22510 : x = y := by
    first
    | (have i₁ := eq22411
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22411
    | exact resolve eq22411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22411
  have eq22747 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22510
       grind)
    | exact superpose eq22510 eq16
    | exact resolve eq16 eq22510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22510
  have eq22753 : False := by grind
  exact eq22753

/-- `Equation828`: `x = x ◇ ((x ◇ y) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation828 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law828 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law828.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
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
  have eq103 : ∀ X0 X3 : G, (M.op X0 (M.op X0 (M.op X3 X0))) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 x) (M.op x X0)) X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq103 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq103
    | exact resolve eq103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq545 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq522
    | (have j0 := eq522 X0 X1
       grind)
    | exact resolve eq522 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq866 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq545 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq545
    | (have j0 := eq545 (σ X1) (σ X0)
       grind)
    | exact resolve eq545 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq866 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq866
    | (have j0 := eq866 X0 X1
       grind)
    | exact resolve eq866 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq12101 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X0)) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq137 (σ X0) (σ (σ X1))
       have i₂ := eq916 X0 X1
       grind)
    | exact superpose eq916 eq137
    | (have j0 := eq137 (σ X0) (σ (σ X1))
       have j1 := eq916 X0 X1
       grind)
    | exact resolve eq137 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq916
  have eq12115 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X0)) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq12101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12101
  have eq12126 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X0)) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12115 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq12115
    | (have j0 := eq12115 X0 X1
       grind)
    | exact resolve eq12115 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12115
  have eq12127 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X0)) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq12126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12126
  have eq12182 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (k (σ X0) (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12127 X0 X1
       have i₂ := eq15 (σ X0) (σ X1)
       grind)
    | exact superpose eq15 eq12127
    | (have j0 := eq12127 X0 X1
       grind)
    | exact resolve eq12127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12127
  have eq12205 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X0)) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12182 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12182
    | (have j0 := eq12182 X0 X1
       grind)
    | exact resolve eq12182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12182
  have eq16932 : ∀ X0 X1 : G, (σ (σ (k (τ X0) X1))) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ X1)) ∨ (σ X0) = (σ (σ (k (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12205 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12205
    | exact resolve eq12205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12205
  have eq17019 : ∀ X0 X1 : G, (σ (k X0 (σ X1))) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ X1)) ∨ (σ X0) = (σ (σ (k (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16932 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq16932
    | (have j0 := eq16932 X0 X1
       grind)
    | exact resolve eq16932 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16932
  have eq17040 : ∀ X0 X1 : G, (σ (k X0 (σ X1))) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (k X0 (σ X1))) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17019 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq17019
    | (have j0 := eq17019 X0 X1
       grind)
    | exact resolve eq17019 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17019
  have eq17068 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17040 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17040
    | exact resolve eq17040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17040
  have eq17345 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17068 (τ X0) (τ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq17068
    | (have j0 := eq17068 (τ X0) (τ (k X0 X1))
       grind)
    | exact resolve eq17068 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq17567 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17345 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17345
    | (have j0 := eq17345 X0 X1
       grind)
    | exact resolve eq17345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17345
  have eq17621 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17567 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq17567
    | (have j0 := eq17567 X0 X1
       grind)
    | exact resolve eq17567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17567
  have eq17670 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17621 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq17621
    | (have j0 := eq17621 X0 X1
       grind)
    | exact resolve eq17621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17621
  have eq17709 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17670 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq17670
    | (have j0 := eq17670 X0 X1
       grind)
    | exact resolve eq17670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17670
  have eq17738 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17709 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17709
    | (have j0 := eq17709 X0 X1
       grind)
    | exact resolve eq17709 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17709
  have eq17763 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17738 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq17738
    | (have j0 := eq17738 X0 X1
       grind)
    | exact resolve eq17738 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17738
  have eq17784 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17763 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17763
    | (have j0 := eq17763 X0 X1
       grind)
    | exact resolve eq17763 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17763
  have eq17851 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17068 X1 X0
       have i₂ := eq17784 X0 X1
       grind)
    | exact superpose eq17784 eq17068
    | (have j0 := eq17068 X1 (M.op X0 X1)
       have j1 := eq17784 X1 X0
       grind)
    | exact resolve eq17068 eq17784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17068
  have eq18046 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17784 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17784
  have eq361376 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq17851 x y
       grind)
    | exact superpose eq17851 eq16
    | (have j1 := eq17851 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq17851 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq17851 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq17851 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq17851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17851
  have eq361436 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq361376
  have eq361535 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq361436
       grind)
    | exact superpose eq361436 eq10
    | exact resolve eq10 eq361436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361436
  have eq361804 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq361535
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq361535
    | exact resolve eq361535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361535
  have eq361805 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq18046 y x
       grind)
    | (have r₁ := eq361804
       have r₂ := eq18046 y x
       grind)
    | exact resolve eq361804 eq18046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18046 eq361804
  have eq361808 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq361805
       grind)
    | exact superpose eq361805 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq361805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361809 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq545 x y
       have i₂ := eq361805
       grind)
    | exact superpose eq361805 eq545
    | (have j0 := eq545 x y
       grind)
    | exact resolve eq545 eq361805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq361805
  have eq361829 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq361809
  have eq361830 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq361808
  have eq361841 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq361830
       grind)
    | exact superpose eq361830 eq107
    | exact resolve eq107 eq361830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq361990 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq361829
       grind)
    | exact superpose eq361829 eq16
    | exact resolve eq16 eq361829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362083 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq361990
       have i₂ := eq361830
       grind)
    | exact superpose eq361830 eq361990
    | exact resolve eq361990 eq361830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361990
  have eq362085 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq362083
  have eq362086 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq362085
  have eq362091 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq362086
       grind)
    | exact superpose eq362086 eq16
    | exact resolve eq16 eq362086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362119 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103 (σ y) (σ x)
       have i₂ := eq362086
       grind)
    | exact superpose eq362086 eq103
    | exact resolve eq103 eq362086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362086
  have eq362169 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq362119
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq362119
    | exact resolve eq362119 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362119
  have eq362195 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq361830 eq362169
    | exact resolve eq362169 eq361830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362169
  have eq362292 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq362195 eq361841
    | exact resolve eq361841 eq362195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361841 eq362195
  have eq362293 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq362292
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq362292
    | exact resolve eq362292 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362292
  have eq362294 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq361830 eq362293
    | exact resolve eq362293 eq361830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361830 eq362293
  have eq362295 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq362294
       have r₂ := eq362091
       grind)
    | exact resolve eq362294 eq362091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362091 eq362294
  have eq362299 : y = (M.op y (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 y x
       have i₂ := eq362295
       grind)
    | exact superpose eq362295 eq103
    | exact resolve eq103 eq362295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362323 : y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 y y
       have i₂ := eq362299
       grind)
    | exact superpose eq362299 eq103
    | exact resolve eq103 eq362299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq362299
  have eq362344 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq362323 eq361829
    | exact resolve eq361829 eq362323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361829 eq362323
  have eq362451 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq362344
  have eq362612 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq362451
       grind)
    | exact superpose eq362451 eq16
    | exact resolve eq16 eq362451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362451
  have eq362710 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq362295 eq362612
    | exact resolve eq362612 eq362295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362295 eq362612
  have eq362711 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq362710
  have eq362745 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq362711
       grind)
    | exact superpose eq362711 eq10
    | exact resolve eq10 eq362711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362711
  have eq363014 : x = y ∨ x = y := by
    first
    | (have i₁ := eq362745
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq362745
    | exact resolve eq362745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362745
  have eq363015 : x = y := by grind
  clear eq363014
  have eq363018 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq363015
       grind)
    | exact superpose eq363015 eq16
    | exact resolve eq16 eq363015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363015
  have eq363019 : False := by grind
  exact eq363019

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq24 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq50 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq47
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq110 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq114 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq110 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq110 X1 X1
       have r₂ := eq55 X1 X1
       grind)
    | exact resolve eq110 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq110
  have eq249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq114 (σ X0) (σ X1)
       grind)
    | exact superpose eq114 eq15
    | exact resolve eq15 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X0 X1
       have i₂ := eq114 X0 X1
       grind)
    | exact superpose eq114 eq249
    | exact resolve eq249 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq249
  have eq258 : False := by grind
  exact eq258
