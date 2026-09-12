import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq90 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq83
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq97
    | exact resolve eq97 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq115 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq410 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq54 X1 x x X0
       grind)
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq590 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq58 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq771 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq910 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq921 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq922 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq924 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq910 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq930 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq924 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq924
    | (have j0 := eq924 X0
       grind)
    | exact resolve eq924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq1993 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq410 X1 X0
       grind)
    | exact superpose eq410 eq14
    | exact resolve eq14 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq2088 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq6853 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1 (M.op X0 X0)
       have i₂ := eq55 X0 X0 X1
       grind)
    | exact superpose eq55 eq590
    | exact resolve eq590 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq590
  have eq6972 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6853 X0 X1
       have i₂ := eq1993 X0 X0
       grind)
    | exact superpose eq1993 eq6853
    | exact resolve eq6853 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6853
  have eq7113 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq438 X1 X0 (M.op X0 X0)
       have i₂ := eq6972 X0 X1
       grind)
    | exact superpose eq6972 eq438
    | exact resolve eq438 eq6972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq6972
  have eq83867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq83867
    | exact resolve eq83867 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83867
  have eq83887 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq83876
       have r₂ := eq29
       grind)
    | exact resolve eq83876 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83876
  have eq84046 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq83887 eq7113
    | exact resolve eq7113 eq83887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83887
  have eq84064 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq84046
  have eq84118 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq84064 eq2088
    | exact resolve eq2088 eq84064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84064
  have eq84251 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq84118
    | exact resolve eq84118 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84118
  have eq84908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq84251 eq98
    | exact resolve eq98 eq84251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq84251
  have eq84924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq84908
  have eq84926 : y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq84924
       have r₂ := eq29
       grind)
    | exact resolve eq84924 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84924
  have eq85085 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7113 x x
       have i₂ := eq84926
       grind)
    | exact superpose eq84926 eq7113
    | exact resolve eq7113 eq84926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7113 eq84926
  have eq85103 : x = (M.op y y) := by grind
  clear eq85085
  have eq85149 : (k x y) = (M.op y x) := by grind
  have eq85158 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2088 y
       have i₂ := eq85103
       grind)
    | exact superpose eq85103 eq2088
    | exact resolve eq2088 eq85103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq85255 : y = (M.op x x) := by
    first
    | (have i₁ := eq1993 y y
       have i₂ := eq85103
       grind)
    | exact superpose eq85103 eq1993
    | exact resolve eq1993 eq85103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993 eq85103
  have eq85291 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq85158
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq85158
    | exact resolve eq85158 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85158
  have eq85606 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq85255
       grind)
    | exact superpose eq85255 eq90
    | exact resolve eq90 eq85255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq85810 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq85606
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq85606
    | exact resolve eq85606 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85606
  have eq86431 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq85291
       grind)
    | exact superpose eq85291 eq74
    | exact resolve eq74 eq85291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85291
  have eq86465 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq22 eq86431
    | exact resolve eq86431 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86431
  have eq93365 : (τ (σ y)) = (k x x) ∨ x = y := by
    first
    | exact superpose eq85810 eq51
    | exact resolve eq51 eq85810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq93408 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq93365
    | exact resolve eq93365 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93365
  have eq93633 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq930 x
       have i₂ := eq93408
       grind)
    | exact superpose eq93408 eq930
    | (have j0 := eq930 x
       grind)
    | exact resolve eq930 eq93408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930 eq93408
  have eq93672 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq93633
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq93633
    | exact resolve eq93633 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq93633
  have eq93696 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq86465 eq93672
    | exact resolve eq93672 eq86465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86465 eq93672
  have eq93712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq93696
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq93696
    | exact resolve eq93696 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93696
  have eq93720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq93712
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq93712
    | exact resolve eq93712 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93712
  have eq93726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq28 eq93720
    | exact resolve eq93720 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93720
  have eq93729 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq93726
       have r₂ := eq29
       grind)
    | exact resolve eq93726 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93726
  have eq93730 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq93729
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq93729
    | exact resolve eq93729 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93729
  have eq93786 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq93730 eq771
    | exact resolve eq771 eq93730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq93921 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq93786
       have r₂ := eq93730
       grind)
    | exact resolve eq93786 eq93730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93730 eq93786
  have eq94126 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq93921 eq85810
    | exact resolve eq85810 eq93921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85810 eq93921
  have eq94156 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq94126
  have eq94179 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq94156 eq31
    | exact resolve eq31 eq94156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq94156
  have eq94410 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq94179
    | exact resolve eq94179 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq94179
  have eq94411 : x = y := by grind
  clear eq94410
  have eq94430 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq94411
       grind)
    | exact superpose eq94411 eq20
    | exact resolve eq20 eq94411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq94431 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq94411
       grind)
    | exact superpose eq94411 eq26
    | exact resolve eq26 eq94411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq94596 : (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq85149
       have i₂ := eq94411
       grind)
    | exact superpose eq94411 eq85149
    | exact resolve eq85149 eq94411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85149
  have eq94609 : y = (k x x) := by
    first
    | (have i₁ := eq94596
       have i₂ := eq85255
       grind)
    | exact superpose eq85255 eq94596
    | exact resolve eq94596 eq85255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94596
  have eq94715 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq94431
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq94431
    | exact resolve eq94431 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94431
  have eq94716 : y = (M.op x y) := by
    first
    | (have i₁ := eq94430
       have i₂ := eq85255
       grind)
    | exact superpose eq85255 eq94430
    | exact resolve eq94430 eq85255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85255 eq94430
  have eq94718 : x = (k x x) := by
    first
    | (have i₁ := eq94609
       have i₂ := eq94411
       grind)
    | exact superpose eq94411 eq94609
    | exact resolve eq94609 eq94411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94609
  have eq94763 : x = (M.op x y) := by
    first
    | (have i₁ := eq94716
       have i₂ := eq94411
       grind)
    | exact superpose eq94411 eq94716
    | exact resolve eq94716 eq94411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94411 eq94716
  have eq94780 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq94715 eq28
    | exact resolve eq28 eq94715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq94715
  have eq95063 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq94763 eq22
    | exact resolve eq22 eq94763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq94763
  have eq95362 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq95063
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95063
    | exact resolve eq95063 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95063
  have eq97379 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq922 x
       have i₂ := eq94718
       grind)
    | exact superpose eq94718 eq922
    | (have j0 := eq922 x
       grind)
    | exact resolve eq922 eq94718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq94718
  have eq97407 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq97379
  have eq97429 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq97407
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq97407
    | exact resolve eq97407 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq97407
  have eq97456 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq95362 eq97429
    | exact resolve eq97429 eq95362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97429
  have eq97773 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq95362 eq94780
    | exact resolve eq94780 eq95362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94780 eq95362
  have eq98104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq97456 eq97773
    | exact resolve eq97773 eq97456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97456 eq97773
  have eq98105 : False := by grind
  exact eq98105

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq131 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq136 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq131
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq131
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq193 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq214 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq223 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op x X0) (M.op (M.op (M.op x x) x) X0) X2
       have i₂ := eq53 x x x X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op y X0)) = X0 := by
    intro X0
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq54 X1 X0 x
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq53 X1 x x X0
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X2) (M.op X0 X1)) (M.op (M.op X1 X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (M.op (M.op X1 X2) (M.op X1 X0)) X0 X2
       have i₂ := eq54 X0 X1 X2
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq497 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (M.op X0 X1) (M.op X0 (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X1 x) (M.op X1 sF4))
       have i₂ := eq54 sF4 X1 x
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq613 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X0 X2) X5) (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq57 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0) X5
       have i₂ := eq53 X1 x x X0
       grind)
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq658 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X3 X1 X2 (M.op (M.op X0 x) (M.op X0 (M.op (M.op X1 X2) X3)))
       have i₂ := eq54 (M.op (M.op X1 X2) X3) X0 x
       grind)
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq57 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1109 : y = (M.op (M.op x y) (M.op (M.op (M.op x y) x) y)) := by
    first
    | (have i₁ := eq214 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq214
    | (have j0 := eq214 x y
       grind)
    | exact resolve eq214 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1246 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y))) := by
    first
    | exact superpose eq27 eq223
    | (have j0 := eq223 (σ x) (σ y)
       grind)
    | exact resolve eq223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq1867 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq417 X1 X0
       grind)
    | exact superpose eq417 eq14
    | exact resolve eq14 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq1957 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq5856 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq420 eq465
    | exact resolve eq465 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq6536 : ∀ X0 X1 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 X0) (M.op X0 X3)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq683 (M.op X1 x) (M.op (M.op X0 X1) x) x
       have i₂ := eq395 X0 X1 x
       grind)
    | exact superpose eq395 eq683
    | exact resolve eq683 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq6590 : ∀ X2 : G, (M.op y X2) = (M.op (M.op (M.op x y) (M.op y X2)) X2) := by
    intro X2
    first
    | exact superpose eq470 eq683
    | exact resolve eq683 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq6680 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0 X1
       grind)
    | exact superpose eq54 eq683
    | exact resolve eq683 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6681 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X1 X0 (M.op X0 X1)
       have i₂ := eq445 X1 X0 X1
       grind)
    | exact superpose eq445 eq683
    | exact resolve eq683 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq6691 : (M.op y y) = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1109 eq683
    | exact resolve eq683 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq6699 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1246 eq683
    | exact resolve eq683 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq1246
  have eq6800 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6680 X0 X1
       have i₂ := eq1867 X0 X0
       grind)
    | exact superpose eq1867 eq6680
    | exact resolve eq6680 eq1867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867 eq6680
  have eq6937 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq446 X1 X0 (M.op X0 X0)
       have i₂ := eq6800 X0 X1
       grind)
    | exact superpose eq6800 eq446
    | exact resolve eq446 eq6800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12699 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X1 X0) X2) X0) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq613 X1 (M.op (M.op (M.op X1 X0) X2) X0) X0 X0
       have i₂ := eq465 X0 (M.op X1 X0) X2 X1
       grind)
    | exact superpose eq465 eq613
    | exact resolve eq613 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq613
  have eq15420 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) X0) (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) X0) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq497 eq54
    | exact resolve eq54 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq497
  have eq15889 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq662 X1 (M.op X0 X2) x x (M.op X0 X1)
       have i₂ := eq658 (M.op (M.op (M.op (M.op X0 X2) x) X1) x) X0 X2 X1
       grind)
    | exact superpose eq658 eq662
    | exact resolve eq662 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq662
  have eq16632 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq446 (M.op X1 X0) X1 X0
       have i₂ := eq15889 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq15889 eq446
    | exact resolve eq446 eq15889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq17168 : ∀ X0 : G, (σ X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ X0)) (σ (k X0 y))) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq193 eq416
    | (have j1 := eq193 X0
       grind)
    | exact resolve eq416 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq416
  have eq76855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq76855
    | exact resolve eq76855 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76855
  have eq76876 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq76865
       have r₂ := eq28
       grind)
    | exact resolve eq76865 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76865
  have eq76904 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq76876 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq76876
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq76876
       grind)
    | exact resolve eq12 eq76876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76876
  have eq77009 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq76904
  have eq77010 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq77009
  have eq77033 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77010 eq99
    | exact resolve eq99 eq77010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77010
  have eq77051 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq77033
  have eq77110 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq77051
  have eq77226 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq77110
    | exact resolve eq77110 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77110
  have eq77829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq77226 eq99
    | exact resolve eq99 eq77226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq77226
  have eq77848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq77829
  have eq77851 : y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq77848
       have r₂ := eq28
       grind)
    | exact resolve eq77848 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77848
  have eq77855 : x = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq414 x
       have i₂ := eq77851
       grind)
    | exact superpose eq77851 eq414
    | exact resolve eq414 eq77851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq77851
  have eq78002 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6691 eq77855
    | exact resolve eq77855 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6691 eq77855
  have eq78958 : x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6937 x x
       have i₂ := eq78002
       grind)
    | exact superpose eq78002 eq6937
    | exact resolve eq6937 eq78002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78002
  have eq78963 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq78958
  have eq79007 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1957 y
       have i₂ := eq78963
       grind)
    | exact superpose eq78963 eq1957
    | exact resolve eq1957 eq78963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78963
  have eq79118 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq79007
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79007
    | exact resolve eq79007 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79007
  have eq80160 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq79118
       grind)
    | exact superpose eq79118 eq73
    | exact resolve eq73 eq79118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79118
  have eq80199 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq80160
    | exact resolve eq80160 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80160
  have eq80270 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq80199 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq80199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq80270
    | exact resolve eq80270 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80270
  have eq80295 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq80284
       have r₂ := eq28
       grind)
    | exact resolve eq80284 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80284
  have eq115051 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq80295 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq80295
       grind)
    | exact resolve eq12 eq80295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80295
  have eq115175 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq115051
  have eq115176 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq115175
  have eq115220 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq115176 eq80199
    | exact resolve eq80199 eq115176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115176
  have eq115232 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq115220
  have eq115305 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq115232
  have eq115445 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq115305
    | exact resolve eq115305 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115305
  have eq116181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq115445 eq80199
    | exact resolve eq80199 eq115445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80199 eq115445
  have eq116194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq116181
  have eq116203 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq116194
       have r₂ := eq28
       grind)
    | exact resolve eq116194 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116194
  have eq116205 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq116203 eq27
    | exact resolve eq27 eq116203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq116206 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq116203 eq30
    | exact resolve eq30 eq116203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq116346 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq116203 eq6699
    | exact resolve eq6699 eq116203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6699
  have eq116439 : y = (M.op x y) := by
    first
    | exact superpose eq31 eq116206
    | exact resolve eq116206 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq116206
  have eq116605 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y (M.op y X0)) X0) := by
    intro X0
    first
    | exact superpose eq116439 eq6590
    | exact resolve eq6590 eq116439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6590
  have eq116688 : ∀ X0 : G, (M.op X0 X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq116605 X0
       have i₂ := eq16632 X0 y
       grind)
    | exact superpose eq16632 eq116605
    | exact resolve eq116605 eq16632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16632 eq116605
  have eq119219 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (k (M.op y X0) X0) := by
    intro X0
    grind
  have eq119223 : ∀ X0 : G, (M.op (M.op y X0) X0) = (k X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1957 X0
       have i₂ := eq116688 X0
       grind)
    | (have i₁ := eq1957 y
       have i₂ := eq116688 y
       grind)
    | exact superpose eq116688 eq1957
    | exact resolve eq1957 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119224 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6800 X0 X1
       have i₂ := eq116688 X0
       grind)
    | (have i₁ := eq6800 y X1
       have i₂ := eq116688 y
       grind)
    | exact superpose eq116688 eq6800
    | exact resolve eq6800 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119346 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6937 X0 X0
       have i₂ := eq116688 X0
       grind)
    | (have i₁ := eq6937 X0 y
       have i₂ := eq116688 X0
       grind)
    | exact superpose eq116688 eq6937
    | exact resolve eq6937 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6937
  have eq120150 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq119346 X0
       have i₂ := eq116688 (M.op y X0)
       grind)
    | exact superpose eq116688 eq119346
    | exact resolve eq119346 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119346
  have eq120234 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) X0) (σ (M.op x y))) X1) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq116203 eq5856
    | exact resolve eq5856 eq116203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5856
  have eq120522 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ (M.op x y)) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq120234 eq15889
    | exact resolve eq15889 eq120234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15889 eq120234
  have eq128911 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6681 X0 X1
       have i₂ := eq116688 (M.op X0 X1)
       grind)
    | exact superpose eq116688 eq6681
    | exact resolve eq6681 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6681
  have eq130006 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6536 X0 X1 X1
       have i₂ := eq128911 X0 X1
       grind)
    | exact superpose eq128911 eq6536
    | exact resolve eq6536 eq128911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536 eq128911
  have eq131482 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq116346
       have i₂ := eq116688 sF1
       grind)
    | exact superpose eq116688 eq116346
    | exact resolve eq116346 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116346
  have eq142534 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op X0 (M.op y X1)) (M.op (M.op X1 X2) (M.op y X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq463 y X1 (M.op X0 (M.op y X1)) X2
       have i₂ := eq130006 X0 (M.op y X1)
       grind)
    | exact superpose eq130006 eq463
    | exact resolve eq463 eq130006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq130006
  have eq142853 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op y X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq142534 X0 X1 x
       have i₂ := eq119224 X1 x
       grind)
    | exact superpose eq119224 eq142534
    | exact resolve eq142534 eq119224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119224 eq142534
  have eq165765 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op y X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12699 X0 X1 (M.op y X0)
       have i₂ := eq142853 (M.op X1 X0) X0
       grind)
    | exact superpose eq142853 eq12699
    | exact resolve eq12699 eq142853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12699 eq142853
  have eq315508 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq116439 eq136
    | exact resolve eq136 eq116439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq315509 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq315508
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq315508
    | exact resolve eq315508 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315508
  have eq315510 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq315509
    | exact resolve eq315509 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq315509
  have eq315511 : y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq116439 eq315510
    | exact resolve eq315510 eq116439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315510
  have eq315512 : y = (M.op x x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq315511
       have i₂ := eq116688 x
       grind)
    | exact superpose eq116688 eq315511
    | exact resolve eq315511 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315511
  have eq315513 : y = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq116439 eq315512
    | exact resolve eq315512 eq116439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315512
  have eq315514 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq315513
  have eq315525 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq315514 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq315514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq116205 eq315525
    | exact resolve eq315525 eq116205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315525
  have eq315557 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq315544
       have r₂ := eq28
       grind)
    | exact resolve eq315544 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315544
  have eq315568 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq315557
       have i₂ := eq116688 sF2
       grind)
    | exact superpose eq116688 eq315557
    | exact resolve eq315557 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315557
  have eq1298281 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq315568 eq120522
    | exact resolve eq120522 eq315568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120522 eq315568
  have eq1299031 : (σ x) = (M.op y (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq131482 eq1298281
    | exact resolve eq1298281 eq131482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298281
  have eq2107212 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) X0) (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op y (M.op (M.op (σ x) X0) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq15420 X0
       have i₂ := eq116688 (M.op (M.op sF2 X0) (M.op sF2 sF4))
       grind)
    | exact superpose eq116688 eq15420
    | exact resolve eq15420 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15420
  have eq2107359 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op y (M.op (M.op (σ x) X0) (M.op (σ x) (M.op (σ x) (σ y))))) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2107212 eq56
    | exact resolve eq56 eq2107212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq2107212
  have eq2108386 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op y (M.op (M.op (σ x) X0) (M.op (σ x) (M.op (σ x) (σ y))))) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq116203 eq2107359
    | exact resolve eq2107359 eq116203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107359
  have eq2206079 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ X0)) (σ (k X0 y))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq116203 eq17168
    | (have j0 := eq17168 X0
       grind)
    | exact resolve eq17168 eq116203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17168
  have eq2206080 : ∀ X0 : G, (σ X0) = (M.op y (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ X0)) (σ (k X0 y))) := by
    intro X0
    first
    | (have i₁ := eq2206079 X0
       have i₂ := eq116688 sF3
       grind)
    | exact superpose eq116688 eq2206079
    | (have j0 := eq2206079 X0
       grind)
    | exact resolve eq2206079 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206079
  have eq2206081 : ∀ X0 : G, (σ X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ X0)) (σ (k X0 y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op y (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq116203 eq2206080
    | (have j0 := eq2206080 X0
       grind)
    | exact resolve eq2206080 eq116203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206080
  have eq4506116 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1299031 eq120150
    | exact resolve eq120150 eq1299031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120150 eq1299031
  have eq4507177 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (M.op x x) := by grind
  clear eq4506116
  have eq4507484 : (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq4507177 eq119219
    | exact resolve eq119219 eq4507177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4507177
  have eq4508889 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq116205 eq4507484
    | exact resolve eq4507484 eq116205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4507484
  have eq4515572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq4508889 eq315514
    | exact resolve eq315514 eq4508889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315514 eq4508889
  have eq4515620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq4515572
  have eq4515631 : y = (M.op x x) := by
    first
    | (have r₁ := eq4515620
       have r₂ := eq28
       grind)
    | exact resolve eq4515620 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4515620
  have eq4515776 : (M.op x y) = (k y x) := by grind
  have eq4515780 : (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq1957 x
       have i₂ := eq4515631
       grind)
    | exact superpose eq4515631 eq1957
    | exact resolve eq1957 eq4515631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq4517008 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq4515780
       have i₂ := eq116688 x
       grind)
    | exact superpose eq116688 eq4515780
    | exact resolve eq4515780 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4515780
  have eq4517010 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq4515776
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4515776
    | exact resolve eq4515776 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4515776
  have eq4517156 : y = (k x y) := by
    first
    | (have i₁ := eq4517008
       have i₂ := eq4515631
       grind)
    | exact superpose eq4515631 eq4517008
    | exact resolve eq4517008 eq4515631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4515631 eq4517008
  have eq4517157 : y = (k y x) := by
    first
    | exact superpose eq116439 eq4517010
    | exact resolve eq4517010 eq116439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116439 eq4517010
  have eq4558994 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq2206081 x
       have i₂ := eq4517156
       grind)
    | exact superpose eq4517156 eq2206081
    | (have j0 := eq2206081 x
       grind)
    | exact resolve eq2206081 eq4517156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206081 eq4517156
  have eq4559097 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq4558994
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4558994
    | exact resolve eq4558994 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558994
  have eq4559160 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq116203 eq4559097
    | exact resolve eq4559097 eq116203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559097
  have eq4559222 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq4559160
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4559160
    | exact resolve eq4559160 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559160
  have eq4559278 : (σ x) = (M.op y (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq131482 eq4559222
    | exact resolve eq4559222 eq131482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131482 eq4559222
  have eq4559327 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op y (σ (M.op x y))) ∨ (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq4559278
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4559278
    | exact resolve eq4559278 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559278
  have eq4559374 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op y (σ (M.op x y))) ∨ (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq116205 eq4559327
    | exact resolve eq4559327 eq116205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559327
  have eq4559395 : (σ x) = (M.op y (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq4559374
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4559374
    | exact resolve eq4559374 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4559374
  have eq4559396 : (σ x) = (M.op y (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4559395
  have eq4559469 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq4517157
       grind)
    | exact superpose eq4517157 eq73
    | exact resolve eq73 eq4517157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq4517157
  have eq4559621 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq116203 eq4559469
    | exact resolve eq4559469 eq116203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559469
  have eq4559692 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq4559621
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4559621
    | exact resolve eq4559621 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4559621
  have eq4559755 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq116203 eq4559692
    | exact resolve eq4559692 eq116203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116203 eq4559692
  have eq4647800 : (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4559396 eq119223
    | exact resolve eq119223 eq4559396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119223 eq4559396
  have eq4649120 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4559755 eq4647800
    | exact resolve eq4647800 eq4559755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4647800
  have eq4649183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq116205 eq4649120
    | exact resolve eq4649120 eq116205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4649120
  have eq4649196 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4649183
       have r₂ := eq28
       grind)
    | exact resolve eq4649183 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4649183
  have eq4664250 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op y (M.op (M.op (σ x) X0) (M.op (σ x) (σ x)))) (σ (M.op x y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq4649196 eq2108386
    | exact resolve eq2108386 eq4649196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108386 eq4649196
  have eq4664415 : (σ (M.op x y)) = (M.op (M.op (M.op y (σ x)) (σ (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq4664250 x
       have i₂ := eq6800 sF2 x
       grind)
    | exact superpose eq6800 eq4664250
    | exact resolve eq4664250 eq6800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6800 eq4664250
  have eq4664731 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4664415
       have i₂ := eq165765 sF2 sF1
       grind)
    | exact superpose eq165765 eq4664415
    | exact resolve eq4664415 eq165765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165765 eq4664415
  have eq4664896 : (σ (M.op x y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq4664731
       have i₂ := eq116688 sF2
       grind)
    | exact superpose eq116688 eq4664731
    | exact resolve eq4664731 eq116688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116688 eq4664731
  have eq4664993 : (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq4664896 eq119219
    | exact resolve eq119219 eq4664896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119219 eq4664896
  have eq4666586 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq4559755 eq4664993
    | exact resolve eq4664993 eq4559755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559755 eq4664993
  have eq4666788 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq116205 eq4666586
    | exact resolve eq4666586 eq116205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116205 eq4666586
  have eq4666865 : False := by grind
  exact eq4666865

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq108 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq108 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq111 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq109 (σ X0)
       grind)
    | exact superpose eq109 eq10
    | exact resolve eq10 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq43
    | exact resolve eq43 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq113 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq73
    | exact resolve eq73 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq114 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq49
    | exact resolve eq49 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq115 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq114
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq114
    | exact resolve eq114 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq113
    | exact resolve eq113 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq112
    | exact resolve eq112 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq118 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq111
    | exact resolve eq111 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq123 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq99
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq99
    | exact resolve eq99 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq124 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq123
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq123
    | exact resolve eq123 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq137 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq134
       have i₂ := eq109 sF1
       grind)
    | exact superpose eq109 eq134
    | exact resolve eq134 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq109 sF0
       grind)
    | exact superpose eq109 eq137
    | exact resolve eq137 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq163 : (σ (k (M.op (M.op x y) (M.op x y)) x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq140 eq39
    | exact resolve eq39 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq176 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq270 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq109 (τ X0)
       grind)
    | exact superpose eq109 eq34
    | exact resolve eq34 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq34
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq371
    | exact resolve eq371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq384 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq382 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq382
    | exact resolve eq382 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq382
  have eq487 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq496 eq14
    | exact resolve eq14 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq521 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq270 eq53
    | exact resolve eq53 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq537 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq274 eq53
    | exact resolve eq53 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq545 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 : G, y = (M.op (M.op (M.op X0 x) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq53 x X0 x
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op (M.op x x) (M.op x sF2))
       have i₂ := eq53 sF2 x x
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 X1 X2 (M.op (M.op X0 x) (M.op X0 (M.op (M.op X1 X2) X3)))
       have i₂ := eq53 (M.op (M.op X1 X2) X3) X0 x
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq829 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq75 X1 X1
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq838 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq829 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq839 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq838 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq841 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq839 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq839 X0 X1
       have r₂ := eq13 X0 (σ X1)
       grind)
    | exact resolve eq839 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq855 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq841
    | (have j0 := eq841 X0 X1
       grind)
    | exact resolve eq841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq1071 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq16
    | exact resolve eq16 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1856 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq487
    | exact resolve eq487 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq2083 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq494 X1 X0
       grind)
    | exact superpose eq494 eq14
    | exact resolve eq14 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2906 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq533 eq545
    | exact resolve eq545 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq545
  have eq2935 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq2906 X0
       have i₂ := eq494 y (M.op x X0)
       grind)
    | exact superpose eq494 eq2906
    | exact resolve eq2906 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2906
  have eq3069 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq537 eq548
    | exact resolve eq548 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq548
  have eq3096 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3069 X0
       have i₂ := eq494 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq494 eq3069
    | exact resolve eq3069 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq3069
  have eq5965 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq2935 eq521
    | exact resolve eq521 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935
  have eq5970 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq3096 eq521
    | exact resolve eq521 eq3096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3096
  have eq6079 : y = (M.op (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq5965 eq54
    | exact resolve eq54 eq5965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq5965
  have eq6149 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5970 eq55
    | exact resolve eq55 eq5970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq5970
  have eq6726 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq745 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq745
    | exact resolve eq745 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6729 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq745 (M.op X1 X0) X1 X0
       have i₂ := eq52 X1 X1 X0 X0
       grind)
    | exact superpose eq52 eq745
    | exact resolve eq745 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq745
  have eq6835 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6726 X0 X1
       have i₂ := eq2083 X0 X0
       grind)
    | exact superpose eq2083 eq6726
    | exact resolve eq6726 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6726
  have eq6895 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq6835 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6835
    | (have j0 := eq6835 x y
       grind)
    | exact resolve eq6835 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6916 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq26 eq6835
    | (have j0 := eq6835 (σ x) (σ y)
       grind)
    | exact resolve eq6835 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6959 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq271 X0 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq6835 (M.op x X0) y
       grind)
    | exact superpose eq6835 eq271
    | exact resolve eq271 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq6961 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq275 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq6835 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq6835 eq275
    | exact resolve eq275 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq9050 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq6959 (M.op x (M.op X0 x))
       have i₂ := eq1856 x X0
       grind)
    | exact superpose eq1856 eq6959
    | exact resolve eq6959 eq1856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9119 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6961 (M.op sF2 (M.op x sF2))
       have i₂ := eq1856 sF2 x
       grind)
    | exact superpose eq1856 eq6961
    | exact resolve eq6961 eq1856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq14302 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op (M.op (M.op X1 X0) X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 X0) X1) X0
       have i₂ := eq6729 X0 X1
       grind)
    | exact superpose eq6729 eq14
    | exact resolve eq14 eq6729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14390 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq14593 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 X0)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14390 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14390
    | (have j0 := eq14390 X0 x
       grind)
    | exact resolve eq14390 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14600 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14390 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq14390
    | (have j0 := eq14390 (τ X0) X1
       grind)
    | exact resolve eq14390 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14627 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq14390 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14390
    | (have j0 := eq14390 y X0
       grind)
    | exact resolve eq14390 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14390
  have eq14709 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14627 X0
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq14627
    | (have j0 := eq14627 X0
       grind)
    | exact resolve eq14627 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14627
  have eq14716 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14600 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq14600
    | (have j0 := eq14600 X0 X1
       grind)
    | exact resolve eq14600 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14600
  have eq14737 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14716 X0 X1
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq14716
    | (have j0 := eq14716 X0 X1
       grind)
    | exact resolve eq14716 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq14716
  have eq14755 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14737 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq14737
    | (have j0 := eq14737 X0 X1
       grind)
    | exact resolve eq14737 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq14737
  have eq16372 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq724 X1 (M.op X0 X2) x x (M.op X0 X1)
       have i₂ := eq720 (M.op (M.op (M.op (M.op X0 X2) x) X1) x) X0 X2 X1
       grind)
    | exact superpose eq720 eq724
    | exact resolve eq724 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq724
  have eq16839 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X1) X2) (M.op (M.op X0 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16372 (M.op (M.op X1 X0) X1) X2 X0
       have i₂ := eq6729 X0 X1
       grind)
    | exact superpose eq6729 eq16372
    | exact resolve eq16372 eq6729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6729
  have eq17122 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq521 (M.op X1 X0) X1 X0
       have i₂ := eq16372 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq16372 eq521
    | exact resolve eq521 eq16372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq16372
  have eq19409 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ x)) = (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq176
    | (have j0 := eq176 X0
       grind)
    | exact resolve eq176 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq176
  have eq19441 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19409 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19409
    | (have j0 := eq19409 y
       grind)
    | exact resolve eq19409 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19409
  have eq19532 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19441
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq19441
    | exact resolve eq19441 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19441
  have eq19547 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq19532
    | exact resolve eq19532 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19532
  have eq19558 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19547
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq19547
    | exact resolve eq19547 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19547
  have eq21003 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq1071 X1
       grind)
    | exact superpose eq1071 eq372
    | (have j0 := eq372 X0 X1
       grind)
    | exact resolve eq372 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq1071
  have eq21019 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ (τ (M.op (σ y) (σ y))) = (M.op y X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq21003
    | (have j0 := eq21003 X0 x
       grind)
    | exact resolve eq21003 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21003
  have eq21082 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (τ (M.op (σ y) (σ y))) = (M.op y X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq36 eq21019
    | (have j0 := eq21019 X0
       grind)
    | exact resolve eq21019 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq21019
  have eq21094 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y y) = (M.op y X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq124 eq21082
    | (have j0 := eq21082 X0
       grind)
    | exact resolve eq21082 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21082
  have eq37618 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op (M.op X0 x) (M.op x y)) (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq9050 eq17122
    | exact resolve eq17122 eq9050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9050
  have eq37642 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq9119 eq17122
    | exact resolve eq17122 eq9119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9119 eq17122
  have eq265184 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14709 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14709
    | (have j0 := eq14709 x
       grind)
    | exact resolve eq14709 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14709
  have eq265405 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq265184
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq265184
    | exact resolve eq265184 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265184
  have eq265427 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq265405
    | exact resolve eq265405 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265405
  have eq265446 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq265427
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq265427
    | exact resolve eq265427 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265427
  have eq265472 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq265446
  have eq265935 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14755 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq14755
    | exact resolve eq14755 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14755
  have eq267611 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq265935 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265935
  have eq285521 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq267611 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq6835 X0 X1
       grind)
    | exact superpose eq6835 eq267611
    | exact resolve eq267611 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6835 eq267611
  have eq286148 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq285521 X0 X1
       grind)
    | (have r₁ := eq285521 X1 X1
       have r₂ := eq2083 X1 X1
       grind)
    | exact resolve eq285521 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083 eq285521
  have eq288176 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq6895 eq286148
    | exact resolve eq286148 eq6895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6895 eq286148
  have eq289276 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq288176 eq163
    | exact resolve eq163 eq288176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288176
  have eq289278 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq20 eq289276
    | exact resolve eq289276 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289276
  have eq629994 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (M.op X0 (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq6149 eq14302
    | exact resolve eq14302 eq6149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6149 eq14302
  have eq635589 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19558 eq629994
    | exact resolve eq629994 eq19558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19558 eq629994
  have eq635987 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq570 eq635589
    | exact resolve eq635589 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq635589
  have eq636012 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq635987
       have r₂ := eq265472
       grind)
    | exact resolve eq635987 eq265472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265472 eq635987
  have eq674965 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op X0 y) X0) (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq6079 eq16839
    | exact resolve eq16839 eq6079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6079 eq16839
  have eq1058592 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14593 y
       have i₂ := eq21094 x
       grind)
    | exact superpose eq21094 eq14593
    | (have j1 := eq21094 x
       grind)
    | exact resolve eq14593 eq21094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14593 eq21094
  have eq1058874 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1058592
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq1058592
    | exact resolve eq1058592 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058592
  have eq1058904 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1058874
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1058874
    | exact resolve eq1058874 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058874
  have eq1058925 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1058904
    | exact resolve eq1058904 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058904
  have eq1058938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1058925
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1058925
    | exact resolve eq1058925 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1058925
  have eq1058947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq1058938
    | exact resolve eq1058938 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1058938
  have eq1058951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1058947
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1058947
    | exact resolve eq1058947 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1058947
  have eq1058954 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1058951
    | exact resolve eq1058951 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058951
  have eq1058955 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1058954
       have r₂ := eq27
       grind)
    | exact resolve eq1058954 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058954
  have eq1059123 : (M.op x y) = (M.op (M.op (M.op (M.op y x) y) (M.op x y)) y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq674965 y
       have i₂ := eq1058955
       grind)
    | exact superpose eq1058955 eq674965
    | exact resolve eq674965 eq1058955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674965 eq1058955
  have eq1059623 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq566 eq1059123
    | exact resolve eq1059123 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq1059123
  have eq1061464 : (τ (σ (M.op x y))) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1059623 eq124
    | exact resolve eq124 eq1059623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1059623
  have eq1062144 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq1061464
    | exact resolve eq1061464 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1061464
  have eq1062145 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq1062144
  have eq1062177 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq503
       have i₂ := eq1062145
       grind)
    | exact superpose eq1062145 eq503
    | exact resolve eq503 eq1062145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq1062145
  have eq1062928 : (σ (k y x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1062177 eq163
    | exact resolve eq163 eq1062177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq1062177
  have eq1063655 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq289278 eq1062928
    | exact resolve eq1062928 eq289278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289278 eq1062928
  have eq1063695 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1063655
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq1063655
    | exact resolve eq1063655 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1063655
  have eq1066819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1063695 eq636012
    | exact resolve eq636012 eq1063695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636012 eq1063695
  have eq1066834 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1066819
       have r₂ := eq27
       grind)
    | exact resolve eq1066819 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066819
  have eq1067827 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1066834 eq115
    | exact resolve eq115 eq1066834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1066834
  have eq1068643 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq1067827
    | exact resolve eq1067827 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1067827
  have eq1068644 : x = (M.op x x) := by grind
  clear eq1068643
  have eq1068666 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq1068644
       grind)
    | exact superpose eq1068644 eq117
    | exact resolve eq117 eq1068644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1068841 : (M.op y y) = (M.op (M.op (M.op x (M.op x y)) (M.op x y)) y) := by
    first
    | (have i₁ := eq37618 x
       have i₂ := eq1068644
       grind)
    | exact superpose eq1068644 eq37618
    | exact resolve eq37618 eq1068644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37618 eq1068644
  have eq1069428 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq6959 eq1068841
    | exact resolve eq1068841 eq6959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6959 eq1068841
  have eq1069512 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1068666
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1068666
    | exact resolve eq1068666 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1068666
  have eq1071125 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq1069428
       grind)
    | exact superpose eq1069428 eq116
    | exact resolve eq116 eq1069428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1069428
  have eq1071837 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq1071125
    | exact resolve eq1071125 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1071125
  have eq1071888 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1069512 eq6916
    | exact resolve eq6916 eq1069512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6916 eq1069512
  have eq1075141 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq1071888 eq37642
    | exact resolve eq37642 eq1071888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37642 eq1071888
  have eq1075621 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6961 eq1075141
    | exact resolve eq1075141 eq6961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6961 eq1075141
  have eq1075703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1071837 eq1075621
    | exact resolve eq1075621 eq1071837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071837 eq1075621
  have eq1075724 : False := by grind
  exact eq1075724

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  clear eq43
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq97
  have eq113 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq102
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq113
  have eq223 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq63 eq14
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq63 eq14
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq64 eq14
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq64 eq14
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61
    | (have j0 := eq61 x X0 X1 y
       grind)
    | exact resolve eq61 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq63 eq61
    | exact resolve eq61 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq64 eq61
    | exact resolve eq61 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq402 eq14
    | exact resolve eq14 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq403 eq14
    | exact resolve eq14 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq61 X1 x x X0
       grind)
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq223 eq62
    | exact resolve eq62 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq441 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq227 eq62
    | exact resolve eq62 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq449 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq63 eq62
    | exact resolve eq62 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq452 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq64 eq62
    | exact resolve eq62 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq573 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq65 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq680 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq681 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq1212 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | (have i₁ := eq372 (M.op x X0) (M.op (M.op (M.op x x) x) X0)
       have i₂ := eq61 x x x X0
       grind)
    | exact superpose eq61 eq372
    | exact resolve eq372 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq1281 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq375 (M.op x X0) (M.op (M.op (M.op x x) x) X0)
       have i₂ := eq61 x x x X0
       grind)
    | exact superpose eq61 eq375
    | exact resolve eq375 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq1524 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq393
    | exact resolve eq393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq1736 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq400 X1 X0
       grind)
    | exact superpose eq400 eq14
    | exact resolve eq14 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1824 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq1736 X0 X0
       grind)
    | exact superpose eq1736 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq1736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2680 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq437 eq449
    | exact resolve eq449 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq449
  have eq2708 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq2680 X0
       have i₂ := eq400 y (M.op x X0)
       grind)
    | exact superpose eq400 eq2680
    | exact resolve eq2680 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2680
  have eq2762 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq441 eq452
    | exact resolve eq452 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq452
  have eq2788 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2762 X0
       have i₂ := eq400 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq400 eq2762
    | exact resolve eq2762 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq2762
  have eq5335 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq2708 eq425
    | exact resolve eq425 eq2708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2708
  have eq5340 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq2788 eq425
    | exact resolve eq425 eq2788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq2788
  have eq6252 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 X1 (M.op X0 X0)
       have i₂ := eq62 X0 X0 X1
       grind)
    | exact superpose eq62 eq573
    | exact resolve eq573 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq6255 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq573 (M.op X1 X0) X1 X0
       have i₂ := eq61 X1 X1 X0 X0
       grind)
    | exact superpose eq61 eq573
    | exact resolve eq573 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq573
  have eq6369 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6252 X0 X1
       have i₂ := eq1736 X0 X0
       grind)
    | exact superpose eq1736 eq6252
    | exact resolve eq6252 eq1736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736 eq6252
  have eq6492 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq224 X0 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq6369 (M.op x X0) y
       grind)
    | exact superpose eq6369 eq224
    | exact resolve eq224 eq6369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq6494 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq228 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq6369 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq6369 eq228
    | exact resolve eq228 eq6369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq6369
  have eq6740 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq681 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq681
    | (have j0 := eq681 (τ X0)
       grind)
    | exact resolve eq681 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6748 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6740 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6740
    | (have j0 := eq6740 X0
       grind)
    | exact resolve eq6740 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6740
  have eq6754 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6748 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6748
    | (have j0 := eq6748 X0
       grind)
    | exact resolve eq6748 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6748
  have eq7682 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq6492 (M.op x (M.op X0 x))
       have i₂ := eq1524 x X0
       grind)
    | exact superpose eq1524 eq6492
    | exact resolve eq6492 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6492
  have eq7741 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6494 (M.op sF2 (M.op x sF2))
       have i₂ := eq1524 sF2 x
       grind)
    | exact superpose eq1524 eq6494
    | exact resolve eq6494 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524 eq6494
  have eq67664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq67672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq67664
    | exact resolve eq67664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67664
  have eq67683 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq67672
       have r₂ := eq27
       grind)
    | exact resolve eq67672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67672
  have eq67707 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq67683 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 (σ y) x
       have r₂ := eq67683
       grind)
    | (have r₁ := eq12 (σ x) x
       have r₂ := eq67683
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq67683
       grind)
    | exact resolve eq12 eq67683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67683
  have eq67812 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq67707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67707
  have eq67822 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq67812 (σ x)
       have j1 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq67812 x
       have r₂ := eq13 X0 x
       grind)
    | (have r₁ := eq67812 X0
       have r₂ := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq67812 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq67812 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67812
  have eq68226 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq67822 eq102
    | exact resolve eq102 eq67822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq67822
  have eq68252 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq68226
    | exact resolve eq68226 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq68226
  have eq68294 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq6754 (σ x)
       grind)
    | (have r₁ := eq68252
       have r₂ := eq6754 y
       grind)
    | exact resolve eq68252 eq6754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68252
  have eq68349 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (σ x) = (k (σ x) X0) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq68294 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 (σ x) x
       have r₂ := eq68294
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq68294
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq68294
       grind)
    | exact resolve eq12 eq68294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68294
  have eq68454 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ x) = (k (σ x) X0) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq68349 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68349
  have eq68463 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq68454 y
       have j1 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq68454 x
       have r₂ := eq13 X0 x
       grind)
    | (have r₁ := eq68454 X0
       have r₂ := eq13 X0 y
       grind)
    | (have r₁ := eq68454 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq68454 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68454
  have eq69013 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq68463 eq49
    | exact resolve eq49 eq68463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq68463
  have eq69055 : x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq69013
    | exact resolve eq69013 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq69013
  have eq69090 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq6754 y
       grind)
    | (have r₁ := eq69055
       have r₂ := eq6754 x
       grind)
    | exact resolve eq69055 eq6754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6754 eq69055
  have eq69156 : y = (M.op (M.op x y) y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq408
       have i₂ := eq69090
       grind)
    | exact superpose eq69090 eq408
    | exact resolve eq408 eq69090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq69178 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ y = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq69090
       grind)
    | exact superpose eq69090 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq69090
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq69090
       grind)
    | exact resolve eq12 eq69090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69183 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1824 y x
       have i₂ := eq69090
       grind)
    | exact superpose eq69090 eq1824
    | (have r₁ := eq1824 y x
       have r₂ := eq69090
       grind)
    | (have r₁ := eq1824 x x
       have r₂ := eq69090
       grind)
    | exact resolve eq1824 eq69090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69281 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq69183 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69183
  have eq69283 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ y = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq69178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69178
  have eq69293 : ∀ X0 : G, y = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq69283 x
       have j1 := eq13 y X0
       grind)
    | (have r₁ := eq69283 x
       have r₂ := eq13 X0 x
       grind)
    | (have r₁ := eq69283 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq69283 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69283
  have eq69450 : (M.op y y) = (M.op (M.op y (M.op x y)) y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq69156 eq6255
    | exact resolve eq6255 eq69156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69156
  have eq69457 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq402 eq69450
    | exact resolve eq69450 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq69450
  have eq69646 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1212 x
       have i₂ := eq69281 X0
       grind)
    | exact superpose eq69281 eq1212
    | (have j1 := eq69281 X0
       grind)
    | exact resolve eq1212 eq69281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq69659 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1824 x X1
       have i₂ := eq69281 X0
       grind)
    | exact superpose eq69281 eq1824
    | (have j1 := eq69281 X1
       grind)
    | (have r₁ := eq1824 x X1
       have r₂ := eq69281 X0
       grind)
    | exact resolve eq1824 eq69281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69281
  have eq69757 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq69659 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69659
  have eq69774 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq69646 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq69646
    | (have j0 := eq69646 X0
       grind)
    | exact resolve eq69646 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq69646
  have eq69796 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq681 y
       have i₂ := eq69293 y
       grind)
    | exact superpose eq69293 eq681
    | (have j0 := eq681 y
       grind)
    | exact resolve eq681 eq69293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69293
  have eq69869 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq69796
  have eq69926 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69869
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq69869
    | exact resolve eq69869 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69869
  have eq70489 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69090
       have i₂ := eq69457
       grind)
    | exact superpose eq69457 eq69090
    | exact resolve eq69090 eq69457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69090 eq69457
  have eq70606 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq70489
  have eq70656 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7682 x
       have i₂ := eq70606
       grind)
    | exact superpose eq70606 eq7682
    | exact resolve eq7682 eq70606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7682
  have eq70663 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1824 x x
       have i₂ := eq70606
       grind)
    | exact superpose eq70606 eq1824
    | (have r₁ := eq1824 x x
       have r₂ := eq70606
       grind)
    | exact resolve eq1824 eq70606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70606
  have eq70761 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq70663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70663
  have eq70773 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5335 eq70656
    | exact resolve eq70656 eq5335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5335 eq70656
  have eq70986 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq681 x
       have i₂ := eq70761 x
       grind)
    | exact superpose eq70761 eq681
    | (have j0 := eq681 x
       grind)
    | exact resolve eq681 eq70761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70761
  have eq71017 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq70986
  have eq71045 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq71017
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq71017
    | exact resolve eq71017 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71017
  have eq71649 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq70773
       grind)
    | exact superpose eq70773 eq103
    | exact resolve eq103 eq70773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq70773
  have eq71780 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq71649
  have eq71786 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq71780
    | exact resolve eq71780 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71780
  have eq72618 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71045 eq1281
    | exact resolve eq1281 eq71045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq71045
  have eq72746 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq72618
    | exact resolve eq72618 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq72618
  have eq79412 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq681 y
       have i₂ := eq69757 X0 y
       grind)
    | exact superpose eq69757 eq681
    | (have j0 := eq681 y
       have j1 := eq69757 X0 x
       grind)
    | exact resolve eq681 eq69757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69757
  have eq79447 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq79412 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79412
  have eq79479 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq79447 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq79447
    | (have j0 := eq79447 X0
       grind)
    | exact resolve eq79447 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79447
  have eq82567 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq69926 eq414
    | exact resolve eq414 eq69926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq69926
  have eq88740 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq82567 eq6255
    | exact resolve eq6255 eq82567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6255 eq82567
  have eq88747 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq403 eq88740
    | exact resolve eq88740 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq88740
  have eq109401 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq88747 eq79479
    | (have j0 := eq79479 X0
       grind)
    | exact resolve eq79479 eq88747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79479 eq88747
  have eq109551 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq109401 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq109401 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq109401 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109401
  have eq109815 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq681 x
       have i₂ := eq109551 x
       grind)
    | exact superpose eq109551 eq681
    | (have j0 := eq681 x
       grind)
    | exact resolve eq681 eq109551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq109551
  have eq109850 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq109815
  have eq109880 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109850
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq109850
    | exact resolve eq109850 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq109850
  have eq110861 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109880 eq7741
    | exact resolve eq7741 eq109880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7741 eq109880
  have eq111003 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5340 eq110861
    | exact resolve eq110861 eq5340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5340 eq110861
  have eq111395 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq111003 eq115
    | exact resolve eq115 eq111003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq111003
  have eq111555 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq111395
  have eq112411 : (k (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq111555
       grind)
    | exact superpose eq111555 eq73
    | exact resolve eq73 eq111555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq112464 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112411
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq112411
    | exact resolve eq112411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112411
  have eq112502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112464 eq71786
    | exact resolve eq71786 eq112464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112464
  have eq112538 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq112502
       have r₂ := eq27
       grind)
    | exact resolve eq112502 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112502
  have eq112540 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq112538 eq27
    | exact resolve eq27 eq112538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112685 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq112538 eq72746
    | exact resolve eq72746 eq112538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72746 eq112538
  have eq112696 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq112685
  have eq113259 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq112696 eq1824
    | (have r₁ := eq1824 (σ y) x
       have r₂ := eq112696
       grind)
    | exact resolve eq1824 eq112696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824 eq112696
  have eq113378 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq113259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113259
  have eq114600 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113378 eq71786
    | exact resolve eq71786 eq113378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71786 eq113378
  have eq114645 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq114600
  have eq114672 : y = (M.op x y) := by
    first
    | (have r₁ := eq114645
       have r₂ := eq112540
       grind)
    | exact resolve eq114645 eq112540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112540 eq114645
  have eq114736 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq114672 eq20
    | exact resolve eq20 eq114672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq114946 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq114672 eq69774
    | (have j0 := eq69774 X0
       grind)
    | exact resolve eq69774 eq114672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69774 eq114672
  have eq114954 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq114946 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq114946 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq114946 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114946
  have eq115053 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq114736
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq114736
    | exact resolve eq114736 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114736
  have eq115730 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111555
       have i₂ := eq114954 y
       grind)
    | exact superpose eq114954 eq111555
    | exact resolve eq111555 eq114954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111555 eq114954
  have eq115820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq115053 eq115730
    | exact resolve eq115730 eq115053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115730
  have eq115886 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq115820
       have r₂ := eq27
       grind)
    | exact resolve eq115820 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115820
  have eq115967 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115886 eq15
    | exact resolve eq15 eq115886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115886
  have eq116064 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq115967
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq115967
    | exact resolve eq115967 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq115967
  have eq116096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115053 eq116064
    | exact resolve eq116064 eq115053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115053 eq116064
  have eq116116 : False := by grind
  exact eq116116

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_x_pyx_x_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
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
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq19
    | exact resolve eq19 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq56 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X0 X1))) = X0 ∨ (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X0 X1))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X0 X1))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) ∨ (k X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq60 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq29
    | exact resolve eq29 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq230 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X2 (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X1 (M.op X0 X1)) X2) = (k X2 (M.op X1 (M.op X0 X1))) ∨ (k X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X1 (M.op X0 X1))
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq12
    | (have j0 := eq12 X2 (M.op X1 (M.op X0 X1))
       have j1 := eq57 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X0 X1))
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq308 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op X2 X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq332 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq308
    | (have j0 := eq308 X0 X1
       grind)
    | exact resolve eq308 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq308
  have eq340 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq332 X0 X1
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq332 X1 X0
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq332 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq332
  have eq385 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq340 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq340
    | exact resolve eq340 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq340 (σ X1) X0
       grind)
    | exact superpose eq340 eq15
    | (have j1 := eq340 (σ X1) X0
       grind)
    | exact resolve eq15 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq440 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq385 (τ X0) X1
       grind)
    | exact superpose eq385 eq19
    | (have j1 := eq385 (τ X0) X1
       grind)
    | exact resolve eq19 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq868 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq440 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq440
    | exact resolve eq440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq921 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq868 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq868
    | (have j0 := eq868 X0 X1
       grind)
    | exact resolve eq868 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq1557 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq395 x y
       grind)
    | exact superpose eq395 eq16
    | (have j1 := eq395 x y
       grind)
    | exact resolve eq16 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1588 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq2096 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X1) = (k X1 (M.op X0 (M.op X1 X0))) ∨ (k X1 (M.op X0 (M.op X1 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq230 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq2100 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X1 X0))) = X1 ∨ (k X1 (M.op X0 (M.op X1 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2096 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq2096
    | (have j0 := eq2096 X0 X1
       grind)
    | exact resolve eq2096 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096
  have eq2101 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X1 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq2164 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op (σ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op X1 (M.op (σ X0) X1))
       have i₂ := eq2101 X1 (σ X0)
       grind)
    | exact superpose eq2101 eq29
    | exact resolve eq29 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2181 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (M.op (σ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2164 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2164
    | exact resolve eq2164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164
  have eq2329 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq310 X0 X1 X2
       grind)
    | exact superpose eq310 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq310 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq310 X0 X1 X2
       grind)
    | exact resolve eq13 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq2340 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2329 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329
  have eq2346 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (M.op (σ X2) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2340 X0 X1 X2
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq2340
    | (have j0 := eq2340 X0 X1 X2
       grind)
    | exact resolve eq2340 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2340
  have eq2367 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (σ (M.op X2 X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2346 X0 X1 X2
       have i₂ := eq40 X2
       grind)
    | exact superpose eq40 eq2346
    | (have j0 := eq2346 X0 X1 X2
       grind)
    | exact resolve eq2346 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2346
  have eq2368 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (σ (M.op X2 X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2367 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367
  have eq2424 : ∀ X0 X1 X2 : G, (τ (k (σ X0) X2)) = (k (k X0 (τ (τ (M.op X1 (M.op (σ (σ X0)) X1))))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X0 (τ (M.op X1 (M.op (σ (σ X0)) X1))) X2
       have i₂ := eq2181 (σ X0) X1
       grind)
    | exact superpose eq2181 eq60
    | exact resolve eq60 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq2445 : ∀ X0 X1 X2 : G, (k X0 (τ X2)) = (k (k X0 (τ (τ (M.op X1 (M.op (σ (σ X0)) X1))))) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2424 X0 X1 X2
       have i₂ := eq29 X0 X2
       grind)
    | exact superpose eq29 eq2424
    | exact resolve eq2424 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2424
  have eq66039 : ∀ X0 X1 X2 : G, (σ (k X0 (τ X1))) = (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2)))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2)))) (σ (τ X1))) ∨ (σ (k X0 (τ X1))) = (M.op (σ (τ X1)) (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2368 X0 (τ (M.op X1 (M.op (σ (σ X0)) X1))) (τ X2)
       have i₂ := eq2445 X0 X1 X2
       grind)
    | exact superpose eq2445 eq2368
    | (have j0 := eq2368 X0 (τ (M.op X2 (M.op (σ (σ X0)) X2))) (τ X1)
       grind)
    | exact resolve eq2368 eq2445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2368 eq2445
  have eq66380 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X0 (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2)))) (σ (τ X1))) ∨ (σ (k X0 (τ X1))) = (M.op (σ (τ X1)) (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66039 X0 X1 X2
       have i₂ := eq2181 (σ X0) X2
       grind)
    | exact superpose eq2181 eq66039
    | (have j0 := eq66039 X0 X1 X2
       grind)
    | exact resolve eq66039 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66039
  have eq66440 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2)))) (σ (τ X1))) ∨ (σ (k X0 (τ X1))) = (M.op (σ (τ X1)) (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66380 X0 X1 X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq66380
    | (have j0 := eq66380 X0 X1 X2
       grind)
    | exact resolve eq66380 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66380
  have eq66498 : ∀ X0 X1 X2 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2)))) X1) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 (τ X1))) = (M.op (σ (τ X1)) (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66440 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq66440
    | (have j0 := eq66440 X0 X1 X2
       grind)
    | exact resolve eq66440 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66440
  have eq66554 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (σ (M.op (τ X1) (τ X1))) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 (τ X1))) = (M.op (σ (τ X1)) (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66498 X0 X1 X2
       have i₂ := eq2181 (σ X0) X2
       grind)
    | exact superpose eq2181 eq66498
    | (have j0 := eq66498 X0 X1 X2
       grind)
    | exact resolve eq66498 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66498
  have eq66587 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 (τ X1))) = (M.op (σ (τ X1)) (k (σ X0) (τ (M.op X2 (M.op (σ (σ X0)) X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66554 X0 X1 X2
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq66554
    | (have j0 := eq66554 X0 X1 X2
       grind)
    | exact resolve eq66554 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq66554
  have eq66609 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66587 X0 X1 x
       have i₂ := eq2181 (σ X0) x
       grind)
    | exact superpose eq2181 eq66587
    | (have j0 := eq66587 X0 X1 x
       grind)
    | exact resolve eq66587 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181 eq66587
  have eq66629 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66609 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq66609
    | (have j0 := eq66609 X0 X1
       grind)
    | exact resolve eq66609 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66609
  have eq66644 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66629 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq66629
    | (have j0 := eq66629 X0 X1
       grind)
    | exact resolve eq66629 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq66629
  have eq66658 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq66644 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq66644 X0 (σ X0)
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq66644 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq66644 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66644
  have eq66662 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66658 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66658
    | exact resolve eq66658 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66658
  have eq67222 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1557
       have i₂ := eq66662 y x
       grind)
    | exact superpose eq66662 eq1557
    | (have j1 := eq66662 y x
       grind)
    | exact resolve eq1557 eq66662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq67224 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq66662 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66662
  have eq67226 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq67222
  have eq68121 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1588 x y
       have i₂ := eq67226
       grind)
    | exact superpose eq67226 eq1588
    | (have j0 := eq1588 x y
       grind)
    | exact resolve eq1588 eq67226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588 eq67226
  have eq68133 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq68121
  have eq68134 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq68133
  have eq68999 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68134
       grind)
    | exact superpose eq68134 eq16
    | exact resolve eq16 eq68134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69045 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq67224 (σ y) (σ x)
       have i₂ := eq68134
       grind)
    | exact superpose eq68134 eq67224
    | (have j0 := eq67224 (σ y) (σ x)
       grind)
    | (have r₁ := eq67224 (σ y) (σ x)
       have r₂ := eq68134
       grind)
    | exact resolve eq67224 eq68134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67224 eq68134
  have eq69046 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq69045
  have eq69048 : (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq69046
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq69046
    | exact resolve eq69046 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69046
  have eq69771 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq921 x y
       have i₂ := eq69048
       grind)
    | exact superpose eq69048 eq921
    | (have j0 := eq921 x y
       grind)
    | exact resolve eq921 eq69048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq69048
  have eq69962 : y = (M.op x y) := by
    first
    | (have r₁ := eq69771
       have r₂ := eq68999
       grind)
    | exact resolve eq69771 eq68999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69771
  have eq70171 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq68999
       have i₂ := eq69962
       grind)
    | exact superpose eq69962 eq68999
    | exact resolve eq68999 eq69962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68999 eq69962
  have eq70208 : False := by grind
  exact eq70208

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_y_pyx_y_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X0))) (M.op X0 X0)) X0) = X0 := by
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
  have eq67 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq62 (τ X0)
       grind)
    | exact superpose eq62 eq31
    | exact resolve eq31 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq67
    | exact resolve eq67 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
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
  have eq92 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (M.op X1 (M.op (τ X0) (M.op X1 (τ X0)))) (τ (M.op X0 X0))) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (τ X0) X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq61
    | exact resolve eq61 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq448 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq471 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq448
    | (have j0 := eq448 X0 X1
       grind)
    | exact resolve eq448 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq686 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq471 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq471
    | exact resolve eq471 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq729 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq686
    | (have j0 := eq686 X0 X1
       grind)
    | exact resolve eq686 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq686
  have eq734 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq729 X0 X1
       have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq729 X1 X0
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq729 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq737 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq734
    | exact resolve eq734 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 (σ X1))) = X2 ∨ (k (k X0 (σ X1)) X2) = (M.op X2 (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq734 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq734
    | exact resolve eq734 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq734 (σ X0) X1
       grind)
    | exact superpose eq734 eq15
    | (have j1 := eq734 (σ X0) X1
       grind)
    | exact resolve eq15 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq796 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq737 (τ X1) X0
       grind)
    | exact superpose eq737 eq17
    | (have j1 := eq737 (τ X1) X0
       grind)
    | exact resolve eq17 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq737
  have eq895 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq796 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq796
    | exact resolve eq796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq956 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq895 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq895
    | (have j0 := eq895 X0 X1
       grind)
    | exact resolve eq895 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq1191 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq746 x y
       grind)
    | exact superpose eq746 eq16
    | (have j1 := eq746 x y
       grind)
    | exact resolve eq16 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq746 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq1246 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1211 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1211
    | (have j0 := eq1211 (τ X1) (τ X0)
       grind)
    | exact resolve eq1211 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1256 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1246 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1246
    | (have j0 := eq1246 X0 X1
       grind)
    | exact resolve eq1246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1260 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1256 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1256
    | (have j0 := eq1256 X0 X1
       grind)
    | exact resolve eq1256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1262 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1260 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1260
    | (have j0 := eq1260 X0 X1
       grind)
    | exact resolve eq1260 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq1263 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1262 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1262
    | (have j0 := eq1262 X0 X1
       grind)
    | exact resolve eq1262 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1360 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1191
       have i₂ := eq956 y x
       grind)
    | exact superpose eq956 eq1191
    | (have j1 := eq956 (σ y) (σ x)
       grind)
    | (have r₁ := eq1191
       have r₂ := eq956 y x
       grind)
    | exact resolve eq1191 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1361 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1360
  have eq1365 : x ≠ x ∨ (M.op y y) = (M.op y x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1361
       grind)
    | exact superpose eq1361 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1361
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1361
       grind)
    | exact resolve eq13 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1368 : y = (M.op (M.op x (M.op y x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq1361
       grind)
    | exact superpose eq1361 eq9
    | exact resolve eq9 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : x = (k y x) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1365
  have eq7599 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1211 x y
       have i₂ := eq1369
       grind)
    | exact superpose eq1369 eq1211
    | (have j0 := eq1211 x y
       grind)
    | exact resolve eq1211 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq7612 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq7599
  have eq7613 : (M.op y y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7612
  have eq7622 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq7613
       grind)
    | exact superpose eq7613 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq7613
       grind)
    | exact resolve eq12 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9083 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (k X1 (σ X2)) (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (k (k X1 (σ X2)) X0) = X0 ∨ (k (k X1 (σ X2)) X0) = (M.op X0 (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X1 (σ X2)) X0
       have i₂ := eq738 X1 X2 X0
       grind)
    | exact superpose eq738 eq13
    | (have j0 := eq13 (k X1 (σ X2)) X0
       have j1 := eq738 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) X2
       have r₂ := eq738 X0 X1 X2
       grind)
    | exact resolve eq13 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq9098 : ∀ X0 X1 X2 : G, (M.op (k X1 (σ X2)) (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (k (k X1 (σ X2)) X0) = X0 ∨ (k (k X1 (σ X2)) X0) = (M.op X0 (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq9083 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9083
  have eq9104 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op X0 (k X1 (σ X2))) ∨ (k (k X1 (σ X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq9098 X0 X1 X2
       have j1 := eq12 (k X1 (σ X2)) X0
       grind)
    | (have r₁ := eq9098 X1 X1 X2
       have r₂ := eq12 (k X1 (σ X2)) X1
       grind)
    | (have r₁ := eq9098 (k X1 (σ X2)) X1 X2
       have r₂ := eq12 (k X1 (σ X2)) (k X1 (σ X2))
       grind)
    | exact resolve eq9098 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9098
  have eq10332 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 (σ X1))) ≠ X2 ∨ (k (k X0 (σ X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq9104 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9104
  have eq10390 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X1))) ≠ X2 ∨ (k (σ (k X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10332 (σ X0) X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10332
    | exact resolve eq10332 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10332
  have eq10571 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 X1))) ≠ X2 ∨ (k (σ (M.op X0 X1)) X2) = X2 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10390 X0 X1 X2
       have i₂ := eq956 X0 X1
       grind)
    | exact superpose eq956 eq10390
    | (have j1 := eq956 X1 X0
       grind)
    | (have r₁ := eq10390 X0 X1 X1
       have r₂ := eq956 (σ (k X0 X1)) X1
       grind)
    | exact resolve eq10390 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10390
  have eq14701 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) ≠ X1 ∨ (k (σ X0) X1) = X1 ∨ (M.op X2 (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10571 (M.op X1 (M.op X0 (M.op X1 X0))) X0 X2
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq10571
    | exact resolve eq10571 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10571
  have eq51886 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j0 := eq7622 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7622
  have eq51892 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51886
       grind)
    | exact superpose eq51886 eq16
    | exact resolve eq16 eq51886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51886
  have eq51934 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51892
       have i₂ := eq1361
       grind)
    | exact superpose eq1361 eq51892
    | exact resolve eq51892 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51892
  have eq51949 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq51934
  have eq51955 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op X0 (M.op y (M.op X0 y))) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq14701 y (σ x) X0
       have i₂ := eq51949
       grind)
    | exact superpose eq51949 eq14701
    | (have j0 := eq14701 y (σ x) X0
       grind)
    | (have r₁ := eq14701 y (σ x) x
       have r₂ := eq51949
       grind)
    | exact resolve eq14701 eq51949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14701 eq51949
  have eq51971 : ∀ X0 : G, (σ x) = (k (σ y) (σ x)) ∨ y = (M.op X0 (M.op y (M.op X0 y))) ∨ x = (k y x) := by
    intro X0
    first
    | (have j0 := eq51955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51955
  have eq51984 : ∀ X0 : G, y = (M.op X0 (M.op y (M.op X0 y))) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq51971 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq51971
    | (have j0 := eq51971 X0
       grind)
    | exact resolve eq51971 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51971
  have eq52856 : y = (M.op y y) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq51984 x
       grind)
    | exact superpose eq51984 eq9
    | exact resolve eq9 eq51984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51984
  have eq52930 : ∀ X0 : G, (τ y) = (M.op (M.op (M.op X0 (M.op (τ y) (M.op X0 (τ y)))) (τ y)) (τ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq110 y X0
       have i₂ := eq52856
       grind)
    | exact superpose eq52856 eq110
    | exact resolve eq110 eq52856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq52856
  have eq53008 : (τ y) = (M.op (τ y) (τ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq52930 x
       have i₂ := eq9 (τ y) x
       grind)
    | exact superpose eq9 eq52930
    | exact resolve eq52930 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52930
  have eq53023 : x = (k y x) ∨ (σ x) = (σ (k y x)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq53008
       have i₂ := eq74 y
       grind)
    | exact superpose eq74 eq53008
    | exact resolve eq53008 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq53008
  have eq53148 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq1211 x y
       have i₂ := eq53023
       grind)
    | exact superpose eq53023 eq1211
    | (have j0 := eq1211 x y
       grind)
    | (have r₁ := eq1211 x y
       have r₂ := eq53023
       grind)
    | exact resolve eq1211 eq53023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53150 : x ≠ x ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq1263 y x
       have i₂ := eq53023
       grind)
    | exact superpose eq53023 eq1263
    | (have j0 := eq1263 y x
       grind)
    | (have r₁ := eq1263 y x
       have r₂ := eq53023
       grind)
    | exact resolve eq1263 eq53023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq53023
  have eq53240 : x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ (τ y) = (τ (M.op y y)) := by grind
  clear eq53150
  have eq53242 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (τ y) = (τ (M.op y y)) := by grind
  clear eq53148
  have eq53248 : (σ x) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have j1 := eq1211 x y
       grind)
    | (have r₁ := eq53242
       have r₂ := eq1211 x y
       grind)
    | exact resolve eq53242 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53242
  have eq53254 : (σ (M.op x y)) ≠ (σ x) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53248
       grind)
    | exact superpose eq53248 eq16
    | exact resolve eq16 eq53248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53248
  have eq54448 : (σ x) ≠ (σ x) ∨ (τ y) = (τ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq53254
       have i₂ := eq53240
       grind)
    | exact superpose eq53240 eq53254
    | exact resolve eq53254 eq53240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53240 eq53254
  have eq54470 : (σ x) ≠ (σ x) ∨ (τ y) = (τ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq54448
  have eq54471 : (τ y) = (τ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq54470
  have eq54503 : (M.op y y) = (σ (τ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op y y)
       have i₂ := eq54471
       grind)
    | exact superpose eq54471 eq11
    | exact resolve eq11 eq54471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54471
  have eq54656 : y = (M.op y y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq54503
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq54503
    | exact resolve eq54503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54503
  have eq54669 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq7613
       have i₂ := eq54656
       grind)
    | exact superpose eq54656 eq7613
    | exact resolve eq7613 eq54656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7613 eq54656
  have eq54773 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1211 x y
       grind)
    | (have r₁ := eq54669
       have r₂ := eq1211 x y
       grind)
    | exact resolve eq54669 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211 eq54669
  have eq54787 : y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1368
       have i₂ := eq54773
       grind)
    | exact superpose eq54773 eq1368
    | exact resolve eq1368 eq54773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368 eq54773
  have eq54805 : y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq54787
  have eq55148 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54805
       have i₂ := eq1361
       grind)
    | exact superpose eq1361 eq54805
    | exact resolve eq54805 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54805
  have eq55197 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55148
  have eq55209 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1361
       have i₂ := eq55197
       grind)
    | exact superpose eq55197 eq1361
    | exact resolve eq1361 eq55197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361 eq55197
  have eq55265 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55209
  have eq55269 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55265
       grind)
    | exact superpose eq55265 eq16
    | exact resolve eq16 eq55265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55265
  have eq55368 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq55269
       have r₂ := eq76 x
       grind)
    | exact resolve eq55269 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55269
  have eq55389 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55368
       grind)
    | exact superpose eq55368 eq16
    | exact resolve eq16 eq55368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55395 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq55368
       grind)
    | exact superpose eq55368 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq55368
       grind)
    | exact resolve eq13 eq55368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55407 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq55395
  have eq55419 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq55407
       have i₂ := eq76 y
       grind)
    | exact superpose eq76 eq55407
    | exact resolve eq55407 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq55407
  have eq55428 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq55419
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq55419
    | exact resolve eq55419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55419
  have eq65738 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq92 y (σ x)
       have i₂ := eq55428
       grind)
    | exact superpose eq55428 eq92
    | (have j0 := eq92 y (σ x)
       grind)
    | (have r₁ := eq92 y (σ x)
       have r₂ := eq55428
       grind)
    | exact resolve eq92 eq55428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq55428
  have eq65789 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq65738
  have eq65802 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq65789
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq65789
    | exact resolve eq65789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65789
  have eq65808 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq65802
       have i₂ := eq55368
       grind)
    | exact superpose eq55368 eq65802
    | exact resolve eq65802 eq55368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55368 eq65802
  have eq65809 : (σ x) = (σ (k y x)) := by grind
  clear eq65808
  have eq65826 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq956 y x
       have i₂ := eq65809
       grind)
    | exact superpose eq65809 eq956
    | (have j0 := eq956 y x
       grind)
    | exact resolve eq956 eq65809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956 eq65809
  have eq66043 : x = (M.op x y) := by
    first
    | (have r₁ := eq65826
       have r₂ := eq55389
       grind)
    | exact resolve eq65826 eq55389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65826
  have eq66259 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq55389
       have i₂ := eq66043
       grind)
    | exact superpose eq66043 eq55389
    | exact resolve eq55389 eq66043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55389 eq66043
  have eq66283 : False := by grind
  exact eq66283

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_pxx_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq67
  have eq94 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq434 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq417
    | (have j0 := eq417 X0 X1
       grind)
    | exact resolve eq417 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq639 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq434 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq434
    | exact resolve eq434 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq665 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq639
    | (have j0 := eq639 X0 X1
       grind)
    | exact resolve eq639 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq639
  have eq667 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq665 X0 X1
       have j1 := eq94 X1 X0
       grind)
    | (have r₁ := eq665 X1 X0
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq665 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq665 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq665
  have eq669 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq667 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq667
    | exact resolve eq667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq667 (σ X0) X1
       grind)
    | exact superpose eq667 eq15
    | (have j1 := eq667 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq713 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq669 (τ X1) X0
       grind)
    | exact superpose eq669 eq19
    | (have j1 := eq669 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq669
  have eq806 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq713
    | exact resolve eq713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq855 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq806
    | (have j0 := eq806 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq1009 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq682 x y
       grind)
    | exact superpose eq682 eq16
    | (have j1 := eq682 x y
       grind)
    | exact resolve eq16 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq1029 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1009
       have i₂ := eq855 y x
       grind)
    | exact superpose eq855 eq1009
    | (have j1 := eq855 (σ x) (σ y)
       grind)
    | (have r₁ := eq1009
       have r₂ := eq855 y x
       grind)
    | (have r₁ := eq1009
       have r₂ := eq855 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1009
       have r₂ := eq855 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1009 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq1009
  have eq1030 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1029
  have eq1033 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1030
       grind)
    | exact superpose eq1030 eq16
    | exact resolve eq16 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1034 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1033
       have r₂ := eq78 x
       grind)
    | exact resolve eq1033 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1035 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1034
       grind)
    | exact superpose eq1034 eq16
    | exact resolve eq16 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1036 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1034
       grind)
    | exact superpose eq1034 eq10
    | exact resolve eq10 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1081 : x = y := by
    first
    | (have i₁ := eq1036
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1036
    | exact resolve eq1036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1082 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1035
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq1035
    | exact resolve eq1035 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1035
  have eq1083 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1082
       have i₂ := eq1081
       grind)
    | exact superpose eq1081 eq1082
    | exact resolve eq1082 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq1082
  have eq1084 : False := by grind
  exact eq1084

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyy_pxy_pyy_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq22 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
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
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq134 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq139 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq134 X0 X1
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
  have eq268 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq139 (σ X0) (σ X1)
       grind)
    | exact superpose eq139 eq15
    | exact resolve eq15 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 X1
       have i₂ := eq139 X0 X1
       grind)
    | exact superpose eq139 eq268
    | exact resolve eq268 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq268
  have eq275 : False := by grind
  exact eq275
