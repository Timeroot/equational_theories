import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq111 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 X0) X2) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X2) X1
       have i₂ := eq14 (M.op X0 X0) X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X1) X2)
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X1) X2) X1
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq112 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq112 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq119 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq84
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq84
    | exact resolve eq84 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq120 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq119
    | exact resolve eq119 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq146 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq150 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq147
       have i₂ := eq113 sF1
       grind)
    | exact superpose eq113 eq147
    | exact resolve eq147 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq153 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq150
       have i₂ := eq113 sF0
       grind)
    | exact superpose eq113 eq150
    | exact resolve eq150 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq150
  have eq421 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq631 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X2) X1) = (M.op (M.op (M.op X0 X0) X2) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq111 X0 X1 X2
       grind)
    | (have r₁ := eq111 X0 X1 X2
       have r₂ := eq421 X0 X1
       grind)
    | (have r₁ := eq111 X1 X0 X2
       have r₂ := eq421 X0 X1
       grind)
    | exact resolve eq111 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq667 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq631 (M.op x x) x (M.op X0 (M.op x x))
       have i₂ := eq14 X0 x (M.op x x)
       grind)
    | exact superpose eq14 eq631
    | (have j0 := eq631 X0 X2 X2
       grind)
    | exact resolve eq631 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq1515 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq667 x y
       grind)
    | exact superpose eq667 eq44
    | (have j1 := eq667 x y
       grind)
    | exact resolve eq44 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1536 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1515
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1515
    | exact resolve eq1515 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1515
  have eq1538 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1536
    | exact resolve eq1536 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1536
  have eq1542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1538 eq667
    | (have j0 := eq667 x (σ y)
       grind)
    | exact resolve eq667 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq1538
  have eq1544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1542
    | exact resolve eq1542 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1547 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1544
       have r₂ := eq27
       grind)
    | exact resolve eq1544 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1551 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1547 eq120
    | exact resolve eq120 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1547
  have eq1581 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1551
    | exact resolve eq1551 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1551
  have eq1582 : y = (M.op y y) := by grind
  clear eq1581
  have eq1583 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq1582
       have i₂ := eq421 X0 y
       grind)
    | (have i₁ := eq1582
       have i₂ := eq421 y X0
       grind)
    | exact superpose eq421 eq1582
    | exact resolve eq1582 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq1587 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1582
       grind)
    | exact superpose eq1582 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1582
       grind)
    | exact resolve eq13 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1590 : x = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq1582
       grind)
    | exact superpose eq1582 eq52
    | exact resolve eq52 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1613 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq1587 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587
  have eq1615 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1590
       have i₂ := eq1582
       grind)
    | exact superpose eq1582 eq1590
    | exact resolve eq1590 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582 eq1590
  have eq1659 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X1
       have i₂ := eq1583 X1
       grind)
    | exact superpose eq1583 eq14
    | exact resolve eq14 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1680 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq153
       have i₂ := eq1583 sF0
       grind)
    | exact superpose eq1583 eq153
    | exact resolve eq153 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq1688 : y = (σ y) := by
    first
    | (have i₁ := eq1680
       have i₂ := eq1583 sF1
       grind)
    | exact superpose eq1583 eq1680
    | exact resolve eq1680 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq1700 : ∀ X1 : G, (M.op (M.op y X1) y) = X1 := by
    intro X1
    first
    | (have i₁ := eq1659 x X1
       have i₂ := eq1583 x
       grind)
    | exact superpose eq1583 eq1659
    | exact resolve eq1659 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583 eq1659
  have eq1721 : y = (σ y) := by
    first
    | (have i₁ := eq1688
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1688
    | exact resolve eq1688 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1688
  have eq1735 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1721 eq26
    | exact resolve eq26 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1900 : (k (σ (M.op x y)) (σ y)) = (σ (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq146
       have i₂ := eq1613 sF0
       grind)
    | exact superpose eq1613 eq146
    | exact resolve eq146 eq1613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq1907 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1615 eq1900
    | exact resolve eq1900 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615 eq1900
  have eq1914 : (σ x) = (k (σ (M.op x y)) y) := by
    first
    | exact superpose eq1721 eq1907
    | exact resolve eq1907 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721 eq1907
  have eq1919 : (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq1914
       have i₂ := eq1613 sF1
       grind)
    | exact superpose eq1613 eq1914
    | exact resolve eq1914 eq1613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613 eq1914
  have eq1920 : (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq1919
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1919
    | exact resolve eq1919 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1919
  have eq1975 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1920 eq1700
    | exact resolve eq1700 eq1920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700 eq1920
  have eq2007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1735 eq1975
    | exact resolve eq1975 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735 eq1975
  have eq2009 : False := by grind
  exact eq2009

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq391 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq307
    | exact resolve eq307 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq538 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq175 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq558 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X1 X0
       grind)
    | exact superpose eq538 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq538 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq538 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq538 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq538 X2 X0
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq538 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq538 (M.op X1 X1) X0
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq558 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (k X0 (M.op X1 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq567 X2 X1 X0
       have i₂ := eq929 X0 X1
       grind)
    | exact superpose eq929 eq567
    | exact resolve eq567 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq982 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X1) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq563 X2 X0 X1
       have i₂ := eq929 (M.op (M.op X0 X0) X1) X2
       grind)
    | exact superpose eq929 eq563
    | exact resolve eq563 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq929
  have eq1554 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1555 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq538 X0 X1
       grind)
    | exact superpose eq538 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq538 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq538 X1 X1
       grind)
    | exact resolve eq12 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1615 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1616 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1604 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1620 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1615 X0
       have j1 := eq558 X0 X0 X0
       grind)
    | (have r₁ := eq1615 x
       have r₂ := eq558 x x x
       grind)
    | (have r₁ := eq1615 (M.op X0 X0)
       have r₂ := eq558 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | (have r₁ := eq1615 X0
       have r₂ := eq558 X0 (k X0 X0) x
       grind)
    | exact resolve eq1615 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq1615
  have eq1666 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq1620 X0
       grind)
    | exact superpose eq1620 eq538
    | exact resolve eq538 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq1689 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq982 X1 X2 X0
       have i₂ := eq1620 X0
       grind)
    | exact superpose eq1620 eq982
    | exact resolve eq982 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq1719 : ∀ X0 X1 X2 : G, (k (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1689 X0 X1 X2
       have i₂ := eq1620 X1
       grind)
    | exact superpose eq1620 eq1689
    | exact resolve eq1689 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1825 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1620 X0
       have i₂ := eq1666 X1 X0
       grind)
    | exact superpose eq1666 eq1620
    | exact resolve eq1620 eq1666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1854 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1666 (σ X1) X0
       grind)
    | exact superpose eq1666 eq10
    | exact resolve eq10 eq1666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1855 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X1 (σ X1)
       have i₂ := eq1666 (σ X1) X0
       grind)
    | exact superpose eq1666 eq364
    | exact resolve eq364 eq1666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq1856 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq391 X1 X1
       have i₂ := eq1666 (τ X1) X0
       grind)
    | exact superpose eq1666 eq391
    | exact resolve eq391 eq1666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1857 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1666 (τ X1) X0
       grind)
    | exact superpose eq1666 eq34
    | exact resolve eq34 eq1666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1666
  have eq1859 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1857 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq1857
    | exact resolve eq1857 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857
  have eq1860 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1855 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq1855
    | exact resolve eq1855 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq1907 : ∀ X0 X1 : G, (k X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1859 X0 X1
       have i₂ := eq1620 X0
       grind)
    | exact superpose eq1620 eq1859
    | exact resolve eq1859 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq1908 : ∀ X0 X1 : G, (k X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1860 X0 X1
       have i₂ := eq1620 X0
       grind)
    | exact superpose eq1620 eq1860
    | exact resolve eq1860 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860
  have eq2117 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1854 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1854
    | exact resolve eq1854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2149 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (k X2 (σ (k X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq954 X2 x X1
       have i₂ := eq1854 x X0
       grind)
    | exact superpose eq1854 eq954
    | exact resolve eq954 eq1854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq1854
  have eq2244 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) (k X2 (σ (k X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2149 X0 X1 X2
       have i₂ := eq1620 X1
       grind)
    | exact superpose eq1620 eq2149
    | exact resolve eq2149 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2335 : ∀ X0 X2 : G, (τ (k X0 X0)) = (τ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1856 x X2
       have i₂ := eq1856 x X0
       grind)
    | exact superpose eq1856 eq1856
    | exact resolve eq1856 eq1856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2351 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1856 X1 (τ X0)
       have i₂ := eq391 X0 X0
       grind)
    | exact superpose eq391 eq1856
    | exact resolve eq1856 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq2566 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1907 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1907
    | exact resolve eq1907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2697 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1908 (τ X0) X1
       have i₂ := eq391 X0 X0
       grind)
    | exact superpose eq391 eq1908
    | exact resolve eq1908 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3049 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2117 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq2117
    | exact resolve eq2117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117
  have eq3435 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2351 (τ X0) X1
       have i₂ := eq391 X0 X0
       grind)
    | exact superpose eq391 eq2351
    | exact resolve eq2351 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq2351
  have eq3767 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (σ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2566 x X1
       have i₂ := eq2566 X0 x
       grind)
    | exact superpose eq2566 eq2566
    | exact resolve eq2566 eq2566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3800 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1907 x X1
       have i₂ := eq2566 X0 x
       grind)
    | exact superpose eq2566 eq1907
    | exact resolve eq1907 eq2566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4468 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (σ (σ (k X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3049 x X1
       have i₂ := eq2566 X0 x
       grind)
    | exact superpose eq2566 eq3049
    | exact resolve eq3049 eq2566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049
  have eq5408 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (σ (σ (k X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2566 x X1
       have i₂ := eq3800 X0 x
       grind)
    | exact superpose eq3800 eq2566
    | exact resolve eq2566 eq3800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566
  have eq6611 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) x) (M.op x x)) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq1554
       grind)
    | exact superpose eq1554 eq16
    | exact resolve eq16 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq6614 : x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6611 x
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq6611
    | exact resolve eq6611 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6611
  have eq6620 : (M.op x y) = (k y x) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq6614
       have i₂ := eq1620 x
       grind)
    | exact superpose eq1620 eq6614
    | exact resolve eq6614 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6614
  have eq12841 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1555 eq16
    | exact resolve eq16 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq12844 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12841 x
       have i₂ := eq16 sF2 x sF2
       grind)
    | exact superpose eq16 eq12841
    | exact resolve eq12841 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12841
  have eq12850 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq12844
       have i₂ := eq1620 sF2
       grind)
    | exact superpose eq1620 eq12844
    | exact resolve eq12844 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12844
  have eq13543 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1616 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq13545 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13543 X0 X1
       have i₂ := eq1620 X0
       grind)
    | exact superpose eq1620 eq13543
    | (have j0 := eq13543 X0 X1
       grind)
    | exact resolve eq13543 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13543
  have eq44884 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq6620
       grind)
    | exact superpose eq6620 eq39
    | exact resolve eq39 eq6620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6620
  have eq44886 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq44884
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44884
    | exact resolve eq44884 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44884
  have eq44888 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq44886
    | exact resolve eq44886 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44886
  have eq51867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ x = (k x x) := by
    first
    | exact superpose eq44888 eq12850
    | exact resolve eq12850 eq44888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12850 eq44888
  have eq51876 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    first
    | (have r₁ := eq51867
       have r₂ := eq27
       grind)
    | exact resolve eq51867 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51867
  have eq51889 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    first
    | exact superpose eq51876 eq141
    | exact resolve eq141 eq51876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq51918 : ∀ X0 : G, (τ (σ x)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq51876 eq1908
    | exact resolve eq1908 eq51876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51876
  have eq52201 : ∀ X0 : G, x = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq29 eq51918
    | exact resolve eq51918 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51918
  have eq52217 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq51889
    | exact resolve eq51889 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51889
  have eq52218 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq52217
  have eq52310 : ∀ X0 : G, x = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq52201 X0
       have j1 := eq13545 X0 x
       grind)
    | (have r₁ := eq52201 x
       have r₂ := eq13545 X0 x
       grind)
    | (have r₁ := eq52201 X0
       have r₂ := eq13545 X0 x
       grind)
    | exact resolve eq52201 eq13545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13545 eq52201
  have eq52333 : ∀ X0 X1 : G, (k (M.op (k X0 X0) X1) x) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1719 x X0 X1
       have i₂ := eq52218
       grind)
    | exact superpose eq52218 eq1719
    | exact resolve eq1719 eq52218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq52375 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X1 (σ x))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2244 x X0 X1
       have i₂ := eq52218
       grind)
    | exact superpose eq52218 eq2244
    | exact resolve eq2244 eq52218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq52445 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3767 x X0
       have i₂ := eq52218
       grind)
    | exact superpose eq52218 eq3767
    | exact resolve eq3767 eq52218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3767
  have eq52446 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3800 x X0
       have i₂ := eq52218
       grind)
    | exact superpose eq52218 eq3800
    | exact resolve eq3800 eq52218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3800 eq52218
  have eq52556 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52446 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52446
    | (have j0 := eq52446 X0
       grind)
    | exact resolve eq52446 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52446
  have eq52557 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52445 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52445
    | (have j0 := eq52445 X0
       grind)
    | exact resolve eq52445 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52445
  have eq52613 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X1 (σ x))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq52375 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52375
    | (have j0 := eq52375 X0 X1
       grind)
    | exact resolve eq52375 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52375
  have eq52649 : ∀ X1 : G, (k (M.op x X1) x) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq52310 eq52333
    | exact resolve eq52333 eq52310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52333
  have eq52684 : x = (σ (σ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq52310 eq52556
    | exact resolve eq52556 eq52310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52556
  have eq52685 : x = (σ (σ (σ (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq52310 eq52557
    | exact resolve eq52557 eq52310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52557
  have eq52716 : ∀ X1 : G, (M.op x (k X1 (σ x))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq52310 eq52613
    | exact resolve eq52613 eq52310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52310 eq52613
  have eq52765 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq52684 eq52685
    | exact resolve eq52685 eq52684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52684 eq52685
  have eq52800 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq52765
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52765
    | exact resolve eq52765 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52765
  have eq52817 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq52800 eq31
    | exact resolve eq31 eq52800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52896 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq52817
    | exact resolve eq52817 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52817
  have eq52897 : x = (σ x) ∨ x = y := by grind
  clear eq52896
  have eq52904 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq52897
       grind)
    | exact superpose eq52897 eq39
    | exact resolve eq39 eq52897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq52897
  have eq58612 : y = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52649 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52649
    | (have j0 := eq52649 y
       grind)
    | exact resolve eq52649 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52649
  have eq58677 : y = (k (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq52800 eq58612
    | exact resolve eq58612 eq52800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58612
  have eq58737 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq58677 eq52904
    | exact resolve eq52904 eq58677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52904 eq58677
  have eq58740 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58737
  have eq58743 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq58740
    | exact resolve eq58740 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58740
  have eq58746 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq58743
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58743
    | exact resolve eq58743 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58743
  have eq58816 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq58746 eq52716
    | exact resolve eq52716 eq58746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52716 eq58746
  have eq58846 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq58816
  have eq58867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq52800 eq58846
    | exact resolve eq58846 eq52800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52800 eq58846
  have eq58892 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq58867
    | exact resolve eq58867 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58867
  have eq58909 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq58892
       have r₂ := eq27
       grind)
    | exact resolve eq58892 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58892
  have eq58921 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq58909 eq31
    | exact resolve eq31 eq58909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq58909
  have eq59005 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq58921
    | exact resolve eq58921 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq58921
  have eq59006 : x = y := by grind
  clear eq59005
  have eq59040 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq59006
       grind)
    | exact superpose eq59006 eq18
    | exact resolve eq18 eq59006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq59041 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq59006
       grind)
    | exact superpose eq59006 eq24
    | exact resolve eq24 eq59006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq59006
  have eq59066 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq59041
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq59041
    | exact resolve eq59041 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq59041
  have eq59067 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq59040
       have i₂ := eq1620 x
       grind)
    | exact superpose eq1620 eq59040
    | exact resolve eq59040 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59040
  have eq59071 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq59066 eq26
    | exact resolve eq26 eq59066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq59066
  have eq59155 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq59071
       have i₂ := eq1620 sF2
       grind)
    | exact superpose eq1620 eq59071
    | exact resolve eq59071 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620 eq59071
  have eq59193 : ∀ X0 : G, (M.op x y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1825 x X0
       have i₂ := eq59067
       grind)
    | exact superpose eq59067 eq1825
    | exact resolve eq1825 eq59067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59198 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1907 x X0
       have i₂ := eq59067
       grind)
    | exact superpose eq59067 eq1907
    | exact resolve eq1907 eq59067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq59199 : ∀ X0 : G, (k X0 X0) = (τ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1908 x X0
       have i₂ := eq59067
       grind)
    | exact superpose eq59067 eq1908
    | exact resolve eq1908 eq59067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908
  have eq59235 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2335 x X0
       have i₂ := eq59067
       grind)
    | exact superpose eq59067 eq2335
    | exact resolve eq2335 eq59067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335
  have eq59266 : ∀ X0 : G, (k X0 X0) = (τ (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2697 x X0
       have i₂ := eq59067
       grind)
    | exact superpose eq59067 eq2697
    | exact resolve eq2697 eq59067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697
  have eq59287 : ∀ X0 : G, (M.op X0 X0) = (τ (τ (τ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq3435 x X0
       have i₂ := eq59067
       grind)
    | exact superpose eq59067 eq3435
    | exact resolve eq3435 eq59067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3435
  have eq59311 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ (σ (σ (M.op x y)))))) := by
    intro X0
    first
    | (have i₁ := eq4468 x X0
       have i₂ := eq59067
       grind)
    | exact superpose eq59067 eq4468
    | exact resolve eq4468 eq59067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468
  have eq59319 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ (σ (M.op x y)))))) := by
    intro X0
    first
    | (have i₁ := eq5408 x X0
       have i₂ := eq59067
       grind)
    | exact superpose eq59067 eq5408
    | exact resolve eq5408 eq59067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408 eq59067
  have eq59378 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ (σ (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq20 eq59319
    | (have j0 := eq59319 X0
       grind)
    | exact resolve eq59319 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59319
  have eq59382 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ (σ (σ (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq20 eq59311
    | (have j0 := eq59311 X0
       grind)
    | exact resolve eq59311 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59311
  have eq59441 : (τ (M.op x y)) = (τ (τ (τ (M.op x y)))) := by
    first
    | (have i₁ := eq59235 x
       have i₂ := eq59266 x
       grind)
    | exact superpose eq59266 eq59235
    | exact resolve eq59235 eq59266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59235
  have eq59477 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq59198 x
       have i₂ := eq59199 x
       grind)
    | exact superpose eq59199 eq59198
    | exact resolve eq59198 eq59199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59198 eq59199
  have eq59510 : (τ (τ (M.op x y))) = (σ (σ (σ (σ (σ (M.op x y)))))) := by
    first
    | (have i₁ := eq59378 x
       have i₂ := eq59266 x
       grind)
    | exact superpose eq59266 eq59378
    | exact resolve eq59378 eq59266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59266 eq59378
  have eq59513 : (τ (τ (τ (M.op x y)))) = (σ (σ (σ (σ (σ (M.op x y)))))) := by
    first
    | (have i₁ := eq59382 x
       have i₂ := eq59287 x
       grind)
    | exact superpose eq59287 eq59382
    | exact resolve eq59382 eq59287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59287 eq59382
  have eq59581 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq20 eq59477
    | exact resolve eq59477 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq59477
  have eq59604 : (τ (τ (M.op x y))) = (τ (τ (τ (M.op x y)))) := by
    first
    | exact superpose eq59510 eq59513
    | exact resolve eq59513 eq59510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59510 eq59513
  have eq59667 : (τ (M.op x y)) = (τ (τ (M.op x y))) := by
    first
    | exact superpose eq59441 eq59604
    | exact resolve eq59604 eq59441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59441 eq59604
  have eq59715 : (σ (M.op x y)) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq59581 eq59667
    | exact resolve eq59667 eq59581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59581 eq59667
  have eq59742 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq28 eq59715
    | exact resolve eq59715 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq59715
  have eq62321 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq59155 eq1825
    | exact resolve eq1825 eq59155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825 eq59155
  have eq62644 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62321 x
       have i₂ := eq59193 x
       grind)
    | exact superpose eq59193 eq62321
    | exact resolve eq62321 eq59193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59193 eq62321
  have eq63292 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq62644 eq27
    | exact resolve eq27 eq62644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq62644
  have eq63326 : False := by grind
  exact eq63326

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_x_pxx_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = (M.op (M.op (M.op X0 X0) (M.op x y)) x) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq538 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq175 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq175 X2 X3 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X1 X0
       grind)
    | exact superpose eq538 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq538 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq538 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq538 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq538 X2 X0
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq558 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 (M.op X1 X1)
       have i₂ := eq571 (σ X0) X1
       grind)
    | exact superpose eq571 eq364
    | exact resolve eq364 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq576 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq571 (τ X0) X1
       grind)
    | exact superpose eq571 eq34
    | exact resolve eq34 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq589 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq576 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq576
    | exact resolve eq576 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq590 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq575
    | exact resolve eq575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq730 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X0) (k X0 X1)) = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq538 X0 X1
       grind)
    | exact superpose eq538 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq538 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq538 X1 X1
       grind)
    | exact resolve eq12 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq759 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq983 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x
       have i₂ := eq539 x X0 X1
       grind)
    | (have i₁ := eq176 (M.op x x)
       have i₂ := eq539 X0 x x
       grind)
    | exact superpose eq539 eq176
    | exact resolve eq176 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 X0) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq571 X2 x
       have i₂ := eq539 x X0 X1
       grind)
    | (have i₁ := eq571 X0 (M.op X2 X2)
       have i₂ := eq539 X0 X2 X2
       grind)
    | exact superpose eq539 eq571
    | exact resolve eq571 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq1094 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq563 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq563 eq175
    | exact resolve eq175 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq1801 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq764 X0
       grind)
    | exact superpose eq764 eq538
    | (have j1 := eq764 X0
       grind)
    | exact resolve eq538 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1812 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq571 X1 X0
       have i₂ := eq764 X0
       grind)
    | exact superpose eq764 eq571
    | (have j1 := eq764 X0
       grind)
    | exact resolve eq571 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1864 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq764 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq1931 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq178 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq175 X2 X3 X0
       grind)
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2171 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) x) (M.op x x)) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq740
       grind)
    | exact superpose eq740 eq16
    | exact resolve eq16 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq2174 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2171 x
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq2171
    | exact resolve eq2171 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq2218 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538 X2 X1
       have i₂ := eq765 X2 X0
       grind)
    | exact superpose eq765 eq538
    | (have j1 := eq765 X1 X0
       grind)
    | exact resolve eq538 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2290 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq589 (σ (M.op X1 X1)) X1
       have i₂ := eq765 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq765 eq589
    | (have j1 := eq765 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq589 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq2303 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq765 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2311 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2290 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2518 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2311 X2 (M.op X1 X1)
       have i₂ := eq1094 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq2311 X2 (M.op X1 X1)
       have i₂ := eq1094 (M.op X1 X1) X0 X1
       grind)
    | exact superpose eq1094 eq2311
    | exact resolve eq2311 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq2587 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 (M.op X1 X1) X1 X2
       have i₂ := eq2311 (M.op X1 X1) X0
       grind)
    | exact superpose eq2311 eq175
    | exact resolve eq175 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq5401 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq741 eq16
    | exact resolve eq16 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq5404 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5401 x
       have i₂ := eq16 sF2 x sF2
       grind)
    | exact superpose eq16 eq5401
    | exact resolve eq5401 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5401
  have eq7287 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1864 X1
       have i₂ := eq1801 X1 X0
       grind)
    | exact superpose eq1801 eq1864
    | (have j0 := eq1864 X1
       have j1 := eq1801 X1 X1
       grind)
    | (have r₁ := eq1864 (M.op X1 X1)
       have r₂ := eq1801 (M.op X1 X1) X1
       grind)
    | exact resolve eq1864 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq7305 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7287 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7287
  have eq21086 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq176 x
       have i₂ := eq181 X0 x
       grind)
    | exact superpose eq181 eq176
    | exact resolve eq176 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq21087 : ∀ X0 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) x) (M.op X2 y)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq16 X2 x y
       have i₂ := eq181 X0 x
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq27538 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq2174
       grind)
    | exact superpose eq2174 eq39
    | exact resolve eq39 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq27541 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq27538
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27538
    | exact resolve eq27538 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27538
  have eq27543 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq27541
    | exact resolve eq27541 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27541
  have eq33552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27543 eq5404
    | exact resolve eq5404 eq27543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5404
  have eq33561 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq33552
       have r₂ := eq27
       grind)
    | exact resolve eq33552 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33552
  have eq33602 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq33561 eq590
    | exact resolve eq590 eq33561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq33561
  have eq33951 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq33602
    | exact resolve eq33602 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33602
  have eq34056 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq33951 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq33951 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq33951 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33951
  have eq34128 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2303 X0 x
       have i₂ := eq34056 x
       grind)
    | exact superpose eq34056 eq2303
    | (have j0 := eq2303 X0 x
       grind)
    | (have r₁ := eq2303 X0 x
       have r₂ := eq34056 x
       grind)
    | exact resolve eq2303 eq34056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34056
  have eq34146 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq34128 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34128
  have eq34525 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2518 x x X0
       have i₂ := eq34146 (M.op x x)
       grind)
    | exact superpose eq34146 eq2518
    | exact resolve eq2518 eq34146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518
  have eq34537 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2587 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq34146 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq34146 eq2587
    | exact resolve eq2587 eq34146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq34582 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq34146 eq34537
    | exact resolve eq34537 eq34146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34146 eq34537
  have eq34589 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq34525 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34525
    | (have j0 := eq34525 X0
       grind)
    | exact resolve eq34525 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34525
  have eq34872 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq34582
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34582
    | exact resolve eq34582 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34582
  have eq35251 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq34872 eq31
    | exact resolve eq31 eq34872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34872
  have eq35331 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq35251
    | exact resolve eq35251 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35251
  have eq35332 : x = (σ x) ∨ x = y := by grind
  clear eq35331
  have eq35801 : (σ x) = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq35332
       grind)
    | exact superpose eq35332 eq22
    | exact resolve eq22 eq35332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35803 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq35332
       grind)
    | exact superpose eq35332 eq39
    | exact resolve eq39 eq35332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq39853 : (σ (σ (M.op x y))) = (k (σ (σ y)) (σ x)) ∨ x = y ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27543 eq35803
    | exact resolve eq35803 eq27543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27543 eq35803
  have eq39922 : (σ (σ (M.op x y))) = (k (σ (σ y)) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq39853
  have eq39990 : (σ (σ (M.op x y))) = (k (σ (σ y)) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35332 eq39922
    | exact resolve eq39922 eq35332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39922
  have eq40029 : (σ (σ (M.op x y))) = (k (σ (σ x)) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq34589 eq39990
    | (have j1 := eq34589 (σ x)
       grind)
    | exact resolve eq39990 eq34589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34589 eq39990
  have eq40031 : (k (σ x) (σ x)) = (σ (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35801 eq40029
    | exact resolve eq40029 eq35801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40029
  have eq44162 : (k x x) = (τ (σ (σ (M.op x y)))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40031 eq97
    | exact resolve eq97 eq40031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40031
  have eq44190 : (σ (M.op x y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq44162
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq44162
    | exact resolve eq44162 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44162
  have eq44198 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq35332 eq44190
    | exact resolve eq44190 eq35332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44190
  have eq44223 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq44198 eq538
    | exact resolve eq538 eq44198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44233 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq44198 eq571
    | exact resolve eq571 eq44198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq44198
  have eq44990 : ∀ X0 : G, (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq44223 eq97
    | (have j1 := eq44223 X0
       grind)
    | exact resolve eq97 eq44223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq44996 : ∀ X0 X1 : G, (k X0 (σ (M.op x y))) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq44223 eq1812
    | (have j0 := eq1812 (σ x) X1
       have j1 := eq44223 (σ x)
       grind)
    | exact resolve eq1812 eq44223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812 eq44223
  have eq45012 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq44996 X0 (σ x)
       have j1 := eq7305 X0 (σ x)
       grind)
    | (have r₁ := eq44996 (M.op X0 X0) x
       have r₂ := eq7305 X0 (k (M.op X0 X0) (σ (M.op x y)))
       grind)
    | (have r₁ := eq44996 X0 x
       have r₂ := eq7305 (σ x) (σ x)
       grind)
    | (have r₁ := eq44996 X0 X0
       have r₂ := eq7305 X0 (σ x)
       grind)
    | exact resolve eq44996 eq7305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7305 eq44996
  have eq45017 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq28 eq44990
    | (have j0 := eq44990 X0
       grind)
    | exact resolve eq44990 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq44990
  have eq45024 : ∀ X0 : G, (M.op x y) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq35332 eq45017
    | (have j0 := eq45017 X0
       grind)
    | exact resolve eq45017 eq35332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45017
  have eq47691 : ∀ X0 X1 : G, (k X1 (σ (M.op x y))) = X1 ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq45012 (M.op X0 X0)
       grind)
    | exact superpose eq45012 eq538
    | (have j1 := eq45012 X1
       grind)
    | exact resolve eq538 eq45012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45012
  have eq48446 : ∀ X0 X1 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (k X0 (σ x)) = X0 ∨ x = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq45024 eq44233
    | (have j0 := eq44233 X0
       have j1 := eq45024 X1
       grind)
    | exact resolve eq44233 eq45024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44233 eq45024
  have eq48470 : ∀ X0 X1 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (k X0 (σ x)) = X0 ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq48446 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48446
  have eq48486 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq48470 X0 x
       have j1 := eq558 X0 (σ x) X0
       grind)
    | (have r₁ := eq48470 (M.op X0 X0) x
       have r₂ := eq558 X0 (k (M.op X0 X0) (σ x)) x
       grind)
    | (have r₁ := eq48470 X0 X0
       have r₂ := eq558 X0 (σ x) x
       grind)
    | exact resolve eq48470 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq48470
  have eq48515 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq48486 eq2303
    | (have j0 := eq2303 X0 (σ x)
       grind)
    | (have r₁ := eq2303 X0 (σ x)
       have r₂ := eq48486 (σ x)
       grind)
    | exact resolve eq2303 eq48486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48486
  have eq48566 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq48515 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48515
  have eq55077 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq47691 eq2303
    | (have j0 := eq2303 X0 (σ (M.op x y))
       have j1 := eq47691 X1 X1
       grind)
    | (have r₁ := eq2303 X0 (σ (M.op x y))
       have r₂ := eq47691 X0 (σ (M.op x y))
       grind)
    | exact resolve eq2303 eq47691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47691
  have eq55121 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq55077 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55077
  have eq55160 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq48566 eq55121
    | (have j0 := eq55121 X0 X1
       have j1 := eq48566 X1
       grind)
    | exact resolve eq55121 eq48566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48566 eq55121
  have eq58088 : ∀ X0 X2 : G, (M.op x y) = (M.op X2 X2) ∨ (k X0 (σ x)) = X0 ∨ x = y := by
    intro X0 X2
    first
    | (have i₁ := eq988 x x X0
       have i₂ := eq55160 X2 (M.op x x)
       grind)
    | (have i₁ := eq988 X0 X0 X2
       have i₂ := eq55160 (M.op X0 X0) x
       grind)
    | exact superpose eq55160 eq988
    | (have j1 := eq55160 X2 x
       grind)
    | exact resolve eq988 eq55160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq58132 : ∀ X0 : G, (M.op x y) ≠ (σ x) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq55160 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55160
  have eq60004 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) x) (M.op x y)) ∨ (k X1 (σ x)) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq21087 X0 y
       have i₂ := eq58088 X1 y
       grind)
    | (have i₁ := eq21087 X0 x
       have i₂ := eq58088 (M.op x y) x
       grind)
    | exact superpose eq58088 eq21087
    | (have j1 := eq58088 X1 x
       grind)
    | exact resolve eq21087 eq58088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58088
  have eq60148 : ∀ X1 : G, x = y ∨ (k X1 (σ x)) = X1 ∨ x = y := by
    intro X1
    first
    | exact superpose eq21086 eq60004
    | (have j0 := eq60004 x X1
       grind)
    | exact resolve eq60004 eq21086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21086 eq60004
  have eq60149 : ∀ X1 : G, (k X1 (σ x)) = X1 ∨ x = y := by
    intro X1
    first
    | (have j0 := eq60148 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60148
  have eq60509 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq60149 eq2303
    | (have j0 := eq2303 X0 (σ x)
       grind)
    | (have r₁ := eq2303 X0 (σ x)
       have r₂ := eq60149 (σ x)
       grind)
    | exact resolve eq2303 eq60149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2303
  have eq60562 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq60509 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60509
  have eq60777 : ∀ X1 X2 : G, (σ x) = (k X1 X1) ∨ (M.op X2 X2) = X1 ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq2218 X1 x X2
       have i₂ := eq60562 x
       grind)
    | exact superpose eq60562 eq2218
    | (have j0 := eq2218 X1 X1 X2
       grind)
    | exact resolve eq2218 eq60562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218
  have eq60973 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X1
       have i₂ := eq60562 X1
       grind)
    | exact superpose eq60562 eq16
    | exact resolve eq16 eq60562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61001 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) x) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq21087 X0 y
       have i₂ := eq60562 y
       grind)
    | exact superpose eq60562 eq21087
    | exact resolve eq21087 eq60562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21087
  have eq61118 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) (σ x)) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq35332 eq61001
    | exact resolve eq61001 eq35332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35332 eq61001
  have eq61142 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ x = y := by
    intro X1
    first
    | exact superpose eq60562 eq60973
    | exact resolve eq60973 eq60562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60973
  have eq61450 : y = (M.op (M.op (M.op (σ x) (M.op x y)) (σ x)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq60562 eq61118
    | exact resolve eq61118 eq60562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61118
  have eq61701 : y = (M.op (M.op x y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq61142 eq61450
    | exact resolve eq61450 eq61142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61450
  have eq62165 : y = (k (σ x) (M.op x y)) ∨ x = y ∨ (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq61701
       have i₂ := eq11 sF2 sF0
       grind)
    | exact superpose eq11 eq61701
    | (have j1 := eq11 (σ x) (M.op x y)
       grind)
    | exact resolve eq61701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61701
  have eq62186 : y = (k (σ x) (M.op x y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq60562 eq62165
    | exact resolve eq62165 eq60562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62165
  have eq62194 : (σ x) = (M.op (σ x) (M.op x y)) ∨ x = y ∨ y = (k (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq60562 eq62186
    | exact resolve eq62186 eq60562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62186
  have eq172650 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq540 X1 x X2 x
       have i₂ := eq1931 X1 x X2 x X0
       grind)
    | exact superpose eq1931 eq540
    | exact resolve eq540 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq1931
  have eq277974 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y ∨ y = (k (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq62194 eq61142
    | exact resolve eq61142 eq62194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62194
  have eq278053 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (k (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) := by grind
  clear eq277974
  have eq278115 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (k (σ x) (M.op x y)) := by
    first
    | (have j1 := eq58132 (σ x)
       grind)
    | (have r₁ := eq278053
       have r₂ := eq58132 x
       grind)
    | exact resolve eq278053 eq58132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58132 eq278053
  have eq284412 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) y) (M.op x y)) ∨ x = y ∨ y = (k (σ x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq278115 eq983
    | exact resolve eq983 eq278115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983 eq278115
  have eq285077 : x = y ∨ x = y ∨ y = (k (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq284412 x
       have i₂ := eq172650 x sF0 y
       grind)
    | exact superpose eq172650 eq284412
    | exact resolve eq284412 eq172650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172650 eq284412
  have eq285078 : y = (k (σ x) (M.op x y)) ∨ x = y := by grind
  clear eq285077
  have eq285380 : (σ y) = (k (σ (σ x)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq285078 eq41
    | exact resolve eq41 eq285078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq285078
  have eq285393 : (σ y) = (k (σ (σ x)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq285380
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq285380
    | exact resolve eq285380 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285380
  have eq285403 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq35801 eq285393
    | exact resolve eq285393 eq35801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35801 eq285393
  have eq285422 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq285403 eq730
    | (have j0 := eq730 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq730 eq285403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq285428 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq765 eq285422
    | (have j0 := eq285422 X0
       have j1 := eq765 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq285422 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq285422
  have eq285434 : (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) (σ y)) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1801 eq285428
    | (have j1 := eq1801 (σ (M.op x y)) x
       grind)
    | exact resolve eq285428 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285428
  have eq285439 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq60777 eq285434
    | (have j1 := eq60777 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq285434 eq60777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285434
  have eq285443 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1801 eq285439
    | (have j1 := eq1801 (σ (M.op x y)) x
       grind)
    | exact resolve eq285439 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801 eq285439
  have eq285444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq60777 eq285443
    | (have j1 := eq60777 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq285443 eq60777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285443
  have eq285445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq26 eq285444
    | exact resolve eq285444 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285444
  have eq285446 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq285445
       have r₂ := eq27
       grind)
    | exact resolve eq285445 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285445
  have eq285447 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq60777 eq285446
    | (have j1 := eq60777 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq285446 eq60777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60777 eq285446
  have eq285448 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq60562 eq285447
    | exact resolve eq285447 eq60562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285447
  have eq285563 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq285448 eq61142
    | exact resolve eq61142 eq285448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61142 eq285448
  have eq285636 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq285563
  have eq285686 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq60562 eq285636
    | exact resolve eq285636 eq60562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60562 eq285636
  have eq285687 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq285686
  have eq285804 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq285687 eq285403
    | exact resolve eq285403 eq285687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285403 eq285687
  have eq285807 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by grind
  clear eq285804
  have eq285841 : (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq60149 eq285807
    | exact resolve eq285807 eq60149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60149 eq285807
  have eq285965 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq285841 eq31
    | exact resolve eq31 eq285841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq285841
  have eq286203 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq285965
    | exact resolve eq285965 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq285965
  have eq286204 : x = y := by grind
  clear eq286203
  have eq286269 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq286204
       grind)
    | exact superpose eq286204 eq18
    | exact resolve eq18 eq286204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq286270 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq286204
       grind)
    | exact superpose eq286204 eq24
    | exact resolve eq24 eq286204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq286204
  have eq286297 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq286270
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq286270
    | exact resolve eq286270 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq286270
  have eq286298 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq286297 eq26
    | exact resolve eq26 eq286297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq286297
  have eq286484 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq538 x X0
       have i₂ := eq286269
       grind)
    | exact superpose eq286269 eq538
    | exact resolve eq538 eq286269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286593 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2311 X0 x
       have i₂ := eq286269
       grind)
    | exact superpose eq286269 eq2311
    | exact resolve eq2311 eq286269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2311 eq286269
  have eq286919 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq286593
    | (have j0 := eq286593 X0
       grind)
    | exact resolve eq286593 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq286593
  have eq287062 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq286919 x
       have i₂ := eq286484 x
       grind)
    | exact superpose eq286484 eq286919
    | exact resolve eq286919 eq286484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286919
  have eq287818 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq286298 eq538
    | exact resolve eq538 eq286298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq286298
  have eq288335 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq287818 x
       have i₂ := eq286484 x
       grind)
    | exact superpose eq286484 eq287818
    | exact resolve eq287818 eq286484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286484 eq287818
  have eq288934 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq288335 eq27
    | exact resolve eq27 eq288335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq288335
  have eq289044 : False := by grind
  exact eq289044

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq74 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq92
    | (have j0 := eq92 (σ X0) (σ X1)
       grind)
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq44
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq127
  have eq539 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq538
  have eq542 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq539 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq539
       grind)
    | exact resolve eq13 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq572 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq542 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq882 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq8907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118 eq572
    | exact resolve eq572 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq572
  have eq8930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq8907
  have eq8937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8930
       have r₂ := eq129
       grind)
    | exact resolve eq8930 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq8930
  have eq8940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8937
    | exact resolve eq8937 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8937
  have eq8941 : x = (M.op x y) := by
    first
    | (have r₁ := eq8940
       have r₂ := eq27
       grind)
    | exact resolve eq8940 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8940
  have eq8942 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq8941 eq20
    | exact resolve eq20 eq8941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq8946 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq8941 eq74
    | (have r₁ := eq74
       have r₂ := eq8941
       grind)
    | exact resolve eq74 eq8941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq8956 : y = (M.op y y) ∨ x = (k x y) := by grind
  clear eq8946
  have eq8966 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8942
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8942
    | exact resolve eq8942 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8942
  have eq9299 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq8956
       grind)
    | exact superpose eq8956 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq8956
       grind)
    | exact resolve eq13 eq8956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8956
  have eq9394 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq9299 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9299
  have eq10129 : x ≠ (M.op x y) ∨ x = (k x y) := by grind
  clear eq9394
  have eq10131 : x ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10129
    | exact resolve eq10129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10129
  have eq10143 : x = (k x y) := by
    first
    | (have r₁ := eq10131
       have r₂ := eq8941
       grind)
    | exact resolve eq10131 eq8941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8941 eq10131
  have eq10159 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq882 x y
       have i₂ := eq10143
       grind)
    | exact superpose eq10143 eq882
    | (have j0 := eq882 x y
       grind)
    | exact resolve eq882 eq10143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq10143
  have eq10162 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10159
  have eq10167 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10162
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10162
    | exact resolve eq10162 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10162
  have eq10170 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10167
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10167
    | exact resolve eq10167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10167
  have eq10172 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10170
    | exact resolve eq10170 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10170
  have eq10174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8966 eq10172
    | exact resolve eq10172 eq8966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8966 eq10172
  have eq10175 : False := by grind
  exact eq10175

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq48 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq49 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq58 X0 X1
       have r₂ := eq50 X0 X1
       grind)
    | exact resolve eq58 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq58
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq66
  have eq142 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq146 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       have j1 := eq71 X1 X0
       grind)
    | (have r₁ := eq142 X1 X0
       have r₂ := eq71 X0 X1
       grind)
    | (have r₁ := eq142 X1 X1
       have r₂ := eq71 X1 X1
       grind)
    | exact resolve eq142 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq142
  have eq518 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq146 (σ X1) (σ X0)
       grind)
    | exact superpose eq146 eq15
    | exact resolve eq15 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq518 X0 X1
       have i₂ := eq146 X1 X0
       grind)
    | exact superpose eq146 eq518
    | exact resolve eq518 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq518
  have eq524 : False := by grind
  exact eq524

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (k X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq186 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq445 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq323
    | exact resolve eq323 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq647 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X2 (M.op (M.op X1 X1) (k X2 X2))
       have i₂ := eq16 X0 X1 (k X2 X2)
       grind)
    | exact superpose eq16 eq183
    | exact resolve eq183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq647
    | exact resolve eq647 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq654 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (k X0 X0)) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 (τ X0) X1 X2
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq186
    | exact resolve eq186 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X1 x x
       have i₂ := eq652 X0 x x
       grind)
    | (have i₁ := eq652 X0 X1 X1
       have i₂ := eq652 (k X1 X1) X1 x
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X0 X2
       grind)
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X2 X0
       grind)
    | exact superpose eq698 eq186
    | exact resolve eq186 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq773 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq757
    | exact resolve eq757 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq1285 : (M.op x y) = (k y x) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1286 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1287 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1286
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1286
    | exact resolve eq1286 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1288 : (k y y) = (M.op y x) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq1285
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1285
    | exact resolve eq1285 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq3860 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (k X0 X0)) X1) (k X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq773 X2 (τ X0) X1
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq773
    | exact resolve eq773 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq4533 : ∀ X0 : G, (σ y) = (M.op (M.op (k X0 X0) (σ x)) (k (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1287 eq186
    | exact resolve eq186 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq1287
  have eq4538 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4533 x
       have i₂ := eq773 sF3 x sF2
       grind)
    | exact superpose eq773 eq4533
    | exact resolve eq4533 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq4533
  have eq4539 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq4538
  have eq8442 : ∀ X0 : G, y = (M.op (M.op (τ (k X0 X0)) x) (k y y)) ∨ (M.op x y) = (k y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq654 X0 x y
       have i₂ := eq1288
       grind)
    | exact superpose eq1288 eq654
    | exact resolve eq654 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq1288
  have eq8445 : x = y ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq8442 x
       have i₂ := eq3860 x x y
       grind)
    | exact superpose eq3860 eq8442
    | exact resolve eq8442 eq3860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3860 eq8442
  have eq8446 : (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq8445
  have eq8461 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq8446
       grind)
    | exact superpose eq8446 eq39
    | exact resolve eq39 eq8446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8446
  have eq8462 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8461
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8461
    | exact resolve eq8461 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461
  have eq8464 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq8462
    | exact resolve eq8462 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8462
  have eq8467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8464 eq4539
    | exact resolve eq4539 eq8464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4539 eq8464
  have eq8474 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8467
       have r₂ := eq27
       grind)
    | exact resolve eq8467 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8467
  have eq8479 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq8474 eq31
    | exact resolve eq31 eq8474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq8474
  have eq8504 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq8479
    | exact resolve eq8479 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8479
  have eq8505 : x = y := by grind
  clear eq8504
  have eq8508 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8505
       grind)
    | exact superpose eq8505 eq18
    | exact resolve eq18 eq8505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8509 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8505
       grind)
    | exact superpose eq8505 eq24
    | exact resolve eq24 eq8505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8505
  have eq8522 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8509
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8509
    | exact resolve eq8509 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8509
  have eq8523 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq8508
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq8508
    | exact resolve eq8508 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8508
  have eq8526 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8522 eq26
    | exact resolve eq26 eq8522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8522
  have eq8552 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq8526
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq8526
    | exact resolve eq8526 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq8526
  have eq8557 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq8523
       grind)
    | exact superpose eq8523 eq39
    | exact resolve eq39 eq8523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq8523
  have eq8715 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq8557
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8557
    | exact resolve eq8557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8557
  have eq8751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8552 eq8715
    | exact resolve eq8715 eq8552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8552 eq8715
  have eq8774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8751
    | exact resolve eq8751 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8751
  have eq8789 : False := by grind
  exact eq8789

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq101 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq104 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq104 eq104
    | exact resolve eq104 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq120 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq113
    | exact resolve eq113 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq113
  have eq373 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq567 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X4) = (M.op (M.op (M.op X3 X3) X2) (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X4) X3 X2
       have i₂ := eq107 X1 X0 X2 X4
       grind)
    | (have i₁ := eq9 (M.op (M.op X1 X1) (M.op X0 X2)) X1 X0
       have i₂ := eq107 X0 X1 X2 X3
       grind)
    | exact superpose eq107 eq9
    | exact resolve eq9 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq688 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op (M.op X1 X1) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X2) X1 (σ X0)
       have i₂ := eq373 X0 X2
       grind)
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq373 X0 X1
       grind)
    | exact superpose eq373 eq9
    | (have j1 := eq373 X0 X2
       grind)
    | exact resolve eq9 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq691 : ∀ X0 X2 : G, (σ X0) = (σ X2) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq688 X0 x X2
       have i₂ := eq9 (σ X0) x (σ X0)
       grind)
    | exact superpose eq9 eq688
    | (have j0 := eq688 X0 x X2
       grind)
    | exact resolve eq688 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq692 : ∀ X0 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have j0 := eq691 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq13323 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq692 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq692
    | (have j0 := eq692 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq692 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq31211 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op (M.op (σ (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X2 X2) (M.op X3 X1)) X3))) X5) (M.op X6 X5)) = X6 := by
    intro X0 X1 X2 X3 X5 X6
    first
    | (have i₁ := eq101 x X5 X6
       have i₂ := eq567 X2 X3 X1 X0 x
       grind)
    | (have i₁ := eq101 (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X2) X1 X2
       have i₂ := eq567 X2 X2 X2 (M.op X2 X2) x
       grind)
    | exact superpose eq567 eq101
    | exact resolve eq101 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq567
  have eq3565147 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq13323 x y
       grind)
    | exact superpose eq13323 eq16
    | (have j1 := eq13323 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq13323 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq13323 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq13323 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq13323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13323
  have eq3565424 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3565147
  have eq3567919 : ∀ X0 X1 X2 X3 : G, y = (M.op (M.op (σ (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X2 X2) (M.op X3 X1)) X3))) y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31211 X0 X1 X2 X3 y y
       have i₂ := eq3565424
       grind)
    | exact superpose eq3565424 eq31211
    | exact resolve eq31211 eq3565424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3565424
  have eq3567957 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3567919 x x x x
       have i₂ := eq31211 x x x x y x
       grind)
    | (have i₁ := eq3567919 x x x x
       have i₂ := eq31211 x x x x x (M.op (M.op (σ (M.op (M.op (M.op x x) x) (M.op (M.op (M.op x x) (M.op x x)) x))) y) (M.op x y))
       grind)
    | exact superpose eq31211 eq3567919
    | exact resolve eq3567919 eq31211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31211 eq3567919
  have eq3567958 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3567957
  have eq3568073 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3567958
       grind)
    | exact superpose eq3567958 eq10
    | exact resolve eq10 eq3567958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567958
  have eq3568240 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3568073
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3568073
    | exact resolve eq3568073 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568073
  have eq3568241 : x = y := by grind
  clear eq3568240
  have eq3568242 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3568241
       grind)
    | exact superpose eq3568241 eq16
    | exact resolve eq16 eq3568241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568241
  have eq3568243 : False := by grind
  exact eq3568243

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_y_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq100 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq100 (σ X1) (σ X0)
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq100 X1 X0
       grind)
    | exact superpose eq100 eq109
    | (have j0 := eq109 X0 X1
       have j1 := eq100 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq109 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq109
  have eq317 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq95 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq95 (σ X1) X0
       grind)
    | exact superpose eq95 eq22
    | exact resolve eq22 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq95
  have eq2044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq145 x y
       grind)
    | exact superpose eq145 eq16
    | (have j1 := eq145 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq2057 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2044
  have eq7787 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2057
       grind)
    | exact superpose eq2057 eq10
    | exact resolve eq10 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq7800 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7787
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7787
    | exact resolve eq7787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7787
  have eq7801 : x = y := by grind
  clear eq7800
  have eq17737 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7801
       grind)
    | exact superpose eq7801 eq16
    | exact resolve eq16 eq7801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7801
  have eq17738 : False := by grind
  exact eq17738
