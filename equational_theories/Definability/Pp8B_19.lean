import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq47 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq49 (σ X0)
       grind)
    | exact superpose eq49 eq32
    | exact resolve eq32 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq90 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq49 (τ X0)
       grind)
    | exact superpose eq49 eq19
    | exact resolve eq19 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq91 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq90
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq93 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq88
    | exact resolve eq88 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq91
    | exact resolve eq91 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq93
    | exact resolve eq93 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq93
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq99 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  clear eq62
  have eq162 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq26
    | exact resolve eq26 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq146
       have i₂ := eq103 y
       grind)
    | exact superpose eq103 eq146
    | exact resolve eq146 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq630 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq629
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq629
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq629
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq629
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq629 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq631 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq630
  have eq1680 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165 (M.op (τ X0) (τ X0)) X1 X2
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq165
    | exact resolve eq165 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq165
  have eq1726 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1680 X0 X1 X2
       have i₂ := eq82 (τ X0) (τ X0)
       grind)
    | exact superpose eq82 eq1680
    | exact resolve eq1680 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq1733 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1726 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1726
    | exact resolve eq1726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1747 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1733 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq25 X1 X1 X0 X2
       grind)
    | exact superpose eq25 eq1733
    | exact resolve eq1733 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1733
  have eq2059 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1747 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq26 (M.op X0 X1)
       grind)
    | exact superpose eq26 eq1747
    | exact resolve eq1747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747
  have eq6921 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq631
       grind)
    | exact superpose eq631 eq16
    | exact resolve eq16 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq6922 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6921
       have r₂ := eq103 x
       grind)
    | exact resolve eq6921 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6921
  have eq74198 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq82 y X0
       have i₂ := eq6922
       grind)
    | exact superpose eq6922 eq82
    | exact resolve eq82 eq6922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6922
  have eq1708828 : ∀ X0 : G, y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq74198 X0
       grind)
    | exact superpose eq74198 eq10
    | (have j1 := eq74198 X0
       grind)
    | exact resolve eq10 eq74198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74198
  have eq1709462 : ∀ X0 : G, x = y ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq1708828 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1708828
    | (have j0 := eq1708828 X0
       grind)
    | exact resolve eq1708828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708828
  have eq1719390 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1709462 X0
       grind)
    | exact superpose eq1709462 eq16
    | (have j1 := eq1709462 X0
       grind)
    | exact resolve eq16 eq1709462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709462
  have eq1719391 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq1719390 X0
       grind)
    | (have r₁ := eq1719390 X0
       have r₂ := eq103 x
       grind)
    | exact resolve eq1719390 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq1719390
  have eq1719417 : (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1719391 x
       have i₂ := eq2059 x y
       grind)
    | exact superpose eq2059 eq1719391
    | exact resolve eq1719391 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059 eq1719391
  have eq1720310 : (M.op (M.op y y) (M.op y y)) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100 (M.op y y)
       have i₂ := eq1719417
       grind)
    | exact superpose eq1719417 eq100
    | exact resolve eq100 eq1719417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719417
  have eq1721129 : (M.op x x) = (M.op (M.op y y) (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1720310
       have i₂ := eq100 x
       grind)
    | exact superpose eq100 eq1720310
    | exact resolve eq1720310 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq1720310
  have eq1721368 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1721129
       have i₂ := eq82 y y
       grind)
    | exact superpose eq82 eq1721129
    | exact resolve eq1721129 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1721129
  have eq1721369 : y = (M.op x x) := by grind
  clear eq1721368
  have eq1721418 : x = (M.op x y) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq1721369
       grind)
    | exact superpose eq1721369 eq26
    | exact resolve eq26 eq1721369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1721421 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq162 x
       have i₂ := eq1721369
       grind)
    | exact superpose eq1721369 eq162
    | exact resolve eq162 eq1721369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq1721369
  have eq1757778 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1721421
       grind)
    | exact superpose eq1721421 eq16
    | exact resolve eq16 eq1721421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721421
  have eq1758724 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1757778
       have i₂ := eq1721418
       grind)
    | exact superpose eq1721418 eq1757778
    | exact resolve eq1757778 eq1721418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721418 eq1757778
  have eq1758725 : False := by grind
  exact eq1758725

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
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
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq75
    | exact resolve eq75 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq80
    | exact resolve eq80 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq360 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (k X0 X0))) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq14
    | (have j1 := eq62 X0
       grind)
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq441 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq3450 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X0 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq441
    | exact resolve eq441 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq441
  have eq3477 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq28 eq3450
    | (have j0 := eq3450 (σ y) (σ x)
       grind)
    | exact resolve eq3450 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6356 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq360 X0 x
       have i₂ := eq3450 (σ (k X0 X0)) x
       grind)
    | exact superpose eq3450 eq360
    | (have j0 := eq360 X0 x
       grind)
    | exact resolve eq360 eq3450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq11785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq11785
    | exact resolve eq11785 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11785
  have eq11797 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq11786
       have r₂ := eq29
       grind)
    | exact resolve eq11786 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11786
  have eq11822 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq11797 eq3450
    | exact resolve eq3450 eq11797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11797
  have eq11823 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq11822
    | exact resolve eq11822 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11822
  have eq11833 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11823
  have eq12106 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11833
       grind)
    | exact superpose eq11833 eq46
    | exact resolve eq46 eq11833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq11833
  have eq12126 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12106
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12106
    | exact resolve eq12106 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12106
  have eq12461 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12126 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12126
  have eq12462 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12461
  have eq12466 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq12462
    | exact resolve eq12462 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12462
  have eq12467 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq12466
  have eq13151 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq12467 eq3450
    | exact resolve eq3450 eq12467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12467
  have eq13154 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq13151
    | exact resolve eq13151 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13151
  have eq13155 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13154
  have eq13160 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13155 eq29
    | exact resolve eq29 eq13155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13168 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13155 eq3477
    | exact resolve eq3477 eq13155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477
  have eq13183 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq13168
    | exact resolve eq13168 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13168
  have eq13313 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13183
  have eq13495 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13155 eq13313
    | exact resolve eq13313 eq13155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13155 eq13313
  have eq13503 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13495
  have eq13987 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13503 eq81
    | exact resolve eq81 eq13503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq13503
  have eq13999 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq13987
  have eq14009 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq13999
       have r₂ := eq13160
       grind)
    | exact resolve eq13999 eq13160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13999
  have eq14118 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3450 y y
       have i₂ := eq14009
       grind)
    | exact superpose eq14009 eq3450
    | exact resolve eq3450 eq14009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3450 eq14009
  have eq14120 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14118
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14118
    | exact resolve eq14118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14118
  have eq14126 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14120 eq31
    | exact resolve eq31 eq14120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14120
  have eq14251 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14126
    | exact resolve eq14126 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14126
  have eq14252 : x = (M.op x y) ∨ x = y := by grind
  clear eq14251
  have eq14253 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14252 eq22
    | exact resolve eq22 eq14252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14368 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14253
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14253
    | exact resolve eq14253 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14253
  have eq14445 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14368 eq13160
    | (have r₁ := eq13160
       have r₂ := eq14368
       grind)
    | exact resolve eq13160 eq14368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13160 eq14368
  have eq14454 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq14445
  have eq14455 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq14454
  have eq14523 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq14455 eq31
    | exact resolve eq31 eq14455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14455
  have eq14685 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq14523
    | exact resolve eq14523 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq14523
  have eq14752 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14685 eq14252
    | exact resolve eq14252 eq14685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14252 eq14685
  have eq14753 : x = y := by grind
  clear eq14752
  have eq14806 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq14753
       grind)
    | exact superpose eq14753 eq20
    | exact resolve eq20 eq14753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq14807 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq14753
       grind)
    | exact superpose eq14753 eq26
    | exact resolve eq26 eq14753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14753
  have eq14916 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14807
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14807
    | exact resolve eq14807 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14807
  have eq14918 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14916 eq28
    | exact resolve eq28 eq14916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq14916
  have eq15051 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq14806
       grind)
    | exact superpose eq14806 eq64
    | exact resolve eq64 eq14806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq15057 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq14806
  have eq15080 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq15051
    | exact resolve eq15051 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15051
  have eq15089 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq15939 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq15951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14918 eq15939
    | exact resolve eq15939 eq14918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15939
  have eq15964 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15951
       have r₂ := eq29
       grind)
    | exact resolve eq15951 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15951
  have eq15970 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14918 eq15964
    | exact resolve eq15964 eq14918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15964
  have eq15975 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15970 eq29
    | exact resolve eq29 eq15970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15998 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15970 eq15089
    | exact resolve eq15089 eq15970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15089 eq15970
  have eq16166 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15998 eq15080
    | exact resolve eq15080 eq15998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15080 eq15998
  have eq16183 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq16166
  have eq16194 : x = (M.op x y) := by
    first
    | (have r₁ := eq16183
       have r₂ := eq15975
       grind)
    | exact resolve eq16183 eq15975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15975 eq16183
  have eq16214 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16194 eq22
    | exact resolve eq22 eq16194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq16280 : x = (k x x) := by
    first
    | exact superpose eq16194 eq15057
    | exact resolve eq15057 eq16194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15057 eq16194
  have eq16347 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16214
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16214
    | exact resolve eq16214 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16214
  have eq16665 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6356 x
       have i₂ := eq16280
       grind)
    | exact superpose eq16280 eq6356
    | (have j0 := eq6356 x
       grind)
    | exact resolve eq6356 eq16280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6356 eq16280
  have eq16666 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16665
  have eq16675 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16666
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16666
    | exact resolve eq16666 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16666
  have eq16693 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14918 eq16675
    | exact resolve eq16675 eq14918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14918 eq16675
  have eq16707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16347 eq16693
    | exact resolve eq16693 eq16347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16347 eq16693
  have eq16721 : False := by grind
  exact eq16721

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0)
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq852 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
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
  have eq854 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
  have eq991 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x x)) (M.op x x)) ∨ (M.op x y) = (k x y) := by
    intro X0
    first
    | (have i₁ := eq16 y x y
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq16
    | exact resolve eq16 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq992 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq991 x
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq991
    | exact resolve eq991 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq995 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq41
    | exact resolve eq41 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq992
  have eq996 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq995
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq995
    | exact resolve eq995 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq998 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq996
    | exact resolve eq996 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1021 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq854 eq16
    | exact resolve eq16 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq1022 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1021 x
       have i₂ := eq16 sF2 x sF2
       grind)
    | exact superpose eq16 eq1021
    | exact resolve eq1021 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1022 eq998
    | exact resolve eq998 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998 eq1022
  have eq1031 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1025
       have r₂ := eq27
       grind)
    | exact resolve eq1025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1034 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1031 eq32
    | exact resolve eq32 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1031
  have eq1067 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq1034
    | exact resolve eq1034 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1068 : x = y := by grind
  clear eq1067
  have eq1070 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1068
       grind)
    | exact superpose eq1068 eq18
    | exact resolve eq18 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1071 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1068
       grind)
    | exact superpose eq1068 eq24
    | exact resolve eq24 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1068
  have eq1078 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1071
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1071
    | exact resolve eq1071 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1079 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1078 eq26
    | exact resolve eq26 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1078
  have eq1123 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq194 x
       have i₂ := eq1070
       grind)
    | exact superpose eq1070 eq194
    | exact resolve eq194 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq180 x x
       have i₂ := eq1070
       grind)
    | exact superpose eq1070 eq180
    | exact resolve eq180 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1079 eq194
    | exact resolve eq194 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq1137 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1079 eq180
    | exact resolve eq180 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1150 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1123 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1153 : x = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq1124 eq1150
    | exact resolve eq1150 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1155 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1153
       have i₂ := eq1070
       grind)
    | exact superpose eq1070 eq1153
    | exact resolve eq1153 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq1153
  have eq1161 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1124 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | exact resolve eq13 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq1124 eq16
    | exact resolve eq16 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1181 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1136 eq28
    | (have j0 := eq28 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1184 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1137 eq1181
    | exact resolve eq1181 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq1186 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1079 eq1184
    | exact resolve eq1184 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1199 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1137 eq16
    | exact resolve eq16 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1492 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 (σ x)) (σ x)) ∨ (M.op X0 X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1199 X0
       have i₂ := eq28 X0 sF2
       grind)
    | exact superpose eq28 eq1199
    | (have j1 := eq28 X0 (σ x)
       grind)
    | exact resolve eq1199 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1511 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 (σ x)) (σ x)) ∨ (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1079 eq1492
    | (have j0 := eq1492 X0
       grind)
    | exact resolve eq1492 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1549 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1155 eq40
    | exact resolve eq40 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1155
  have eq1551 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1549
    | exact resolve eq1549 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq2454 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1551 eq1511
    | (have j0 := eq1511 (σ (M.op x y))
       grind)
    | exact resolve eq1511 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq2793 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2454 eq28
    | (have j0 := eq28 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq28 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2454
  have eq2800 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1079 eq2793
    | exact resolve eq2793 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq2793
  have eq2801 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2800
  have eq2804 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1551 eq2801
    | exact resolve eq2801 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551 eq2801
  have eq2806 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2804
       have r₂ := eq27
       grind)
    | exact resolve eq2804 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq2828 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2806 eq180
    | exact resolve eq180 eq2806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq2806
  have eq2835 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1137 eq2828
    | exact resolve eq2828 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq2828
  have eq2842 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2835 eq29
    | exact resolve eq29 eq2835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2835
  have eq2879 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2842
    | exact resolve eq2842 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2842
  have eq2880 : x = (M.op x y) := by grind
  clear eq2879
  have eq2887 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq2880
       grind)
    | exact superpose eq2880 eq22
    | exact resolve eq22 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2904 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1161 X0
       have i₂ := eq2880
       grind)
    | exact superpose eq2880 eq1161
    | (have j0 := eq1161 X0
       grind)
    | (have r₁ := eq1161 X0
       have r₂ := eq2880
       grind)
    | exact resolve eq1161 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq2906 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1168 X0
       have i₂ := eq2880
       grind)
    | exact superpose eq2880 eq1168
    | exact resolve eq1168 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq2880
  have eq2913 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq2904 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq2930 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2887 eq20
    | exact resolve eq20 eq2887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2887
  have eq3362 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2913 eq2906
    | exact resolve eq2906 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2906
  have eq3389 : ∀ X0 : G, (M.op x y) = (k (k X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2913 eq3362
    | exact resolve eq3362 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2913 eq3362
  have eq3462 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (k X0 (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3389 eq42
    | exact resolve eq42 eq3389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389
  have eq3465 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (k X0 (M.op x y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq2930 eq3462
    | exact resolve eq3462 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462
  have eq3467 : ∀ X0 : G, (σ (M.op x y)) = (k (k (σ X0) (σ (M.op x y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq42 eq3465
    | exact resolve eq3465 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq3465
  have eq3469 : ∀ X0 : G, (σ (M.op x y)) = (k (k (σ X0) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq2930 eq3467
    | exact resolve eq3467 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467
  have eq3470 : ∀ X0 : G, (σ (M.op x y)) = (k (k (σ X0) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq20 eq3469
    | (have j0 := eq3469 X0
       grind)
    | exact resolve eq3469 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3469
  have eq3471 : ∀ X0 : G, (σ x) = (k (k (σ X0) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq2930 eq3470
    | exact resolve eq3470 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3470
  have eq3517 : ∀ X0 : G, (σ x) = (k (k X0 (σ x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3471 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq3471
    | exact resolve eq3471 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471
  have eq3556 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1186 eq3517
    | exact resolve eq3517 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3517
  have eq3624 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3556 eq1186
    | exact resolve eq1186 eq3556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186 eq3556
  have eq3630 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3624
  have eq3633 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq3630 eq27
    | exact resolve eq27 eq3630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3630
  have eq3674 : False := by grind
  exact eq3674

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq21 (M.op X0 X0)
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq21
    | exact resolve eq21 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq52 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq76 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq108 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq76 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq108 X0
       grind)
    | (have r₁ := eq108 X0
       have r₂ := eq30 X0
       grind)
    | exact resolve eq108 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq108
  have eq110 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109 (M.op X0 X0)
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq109
    | exact resolve eq109 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq113 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq52 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq109 (σ X0)
       grind)
    | exact superpose eq109 eq52
    | exact resolve eq52 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq122 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq110 (τ X0)
       grind)
    | exact superpose eq110 eq19
    | exact resolve eq19 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq123 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq122 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq122
    | exact resolve eq122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq159 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq123 (τ X0)
       grind)
    | exact superpose eq123 eq19
    | exact resolve eq19 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq160 : ∀ X0 : G, (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq159 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq159
    | exact resolve eq159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq243 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq44
    | (have j0 := eq44 X2 X2
       grind)
    | exact resolve eq44 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq300 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq20 X1 X1 X0 X2
       grind)
    | exact superpose eq20 eq31
    | exact resolve eq31 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31
  have eq407 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq300 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq21 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq300
    | exact resolve eq300 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq300
  have eq561 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq160 (τ X0)
       grind)
    | exact superpose eq160 eq19
    | exact resolve eq19 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 : G, (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq561 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq561
    | exact resolve eq561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq4568 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0)) ∨ (σ X1) = (M.op (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq243 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))) X0 X1
       have i₂ := eq160 (τ X0)
       grind)
    | exact superpose eq160 eq243
    | (have j0 := eq243 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))) X0 X1
       grind)
    | exact resolve eq243 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq243
  have eq4631 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4568 X0 X1
       have i₂ := eq562 X0
       grind)
    | exact superpose eq562 eq4568
    | (have j0 := eq4568 X0 X1
       grind)
    | exact resolve eq4568 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4568
  have eq4648 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4631 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq4631
    | (have j0 := eq4631 X0 X1
       grind)
    | exact resolve eq4631 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4631
  have eq4663 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4648 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq4648 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq4648 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4648
  have eq4674 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4663 X0 X1
       have i₂ := eq562 X0
       grind)
    | exact superpose eq562 eq4663
    | (have j0 := eq4663 X0 X1
       grind)
    | exact resolve eq4663 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq4663
  have eq6160 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4674 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4674
    | exact resolve eq4674 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6213 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4674 (σ X1) X0
       grind)
    | exact superpose eq4674 eq15
    | (have j1 := eq4674 (σ X1) X0
       grind)
    | exact resolve eq15 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4674
  have eq6339 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq6160 (τ X0) X1
       grind)
    | exact superpose eq6160 eq19
    | (have j1 := eq6160 (τ X0) X1
       grind)
    | exact resolve eq19 eq6160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq27127 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6339 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6339
    | exact resolve eq6339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339
  have eq27241 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27127 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq27127
    | (have j0 := eq27127 X0 X1
       grind)
    | exact resolve eq27127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27127
  have eq104997 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6213 x y
       grind)
    | exact superpose eq6213 eq16
    | (have j1 := eq6213 x y
       grind)
    | exact resolve eq16 eq6213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6213
  have eq105639 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq104997
       have i₂ := eq27241 x y
       grind)
    | exact superpose eq27241 eq104997
    | (have j1 := eq27241 (σ x) (σ y)
       grind)
    | (have r₁ := eq104997
       have r₂ := eq27241 x y
       grind)
    | exact resolve eq104997 eq27241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27241
  have eq105642 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq105639
  have eq105666 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq109 y
       have i₂ := eq105642
       grind)
    | exact superpose eq105642 eq109
    | exact resolve eq109 eq105642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq105725 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq407 y y
       have i₂ := eq105642
       grind)
    | exact superpose eq105642 eq407
    | exact resolve eq407 eq105642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105642
  have eq106487 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104997
       have i₂ := eq105666
       grind)
    | exact superpose eq105666 eq104997
    | exact resolve eq104997 eq105666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104997 eq105666
  have eq106496 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq106487
  have eq112982 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq106496
       have i₂ := eq105725
       grind)
    | exact superpose eq105725 eq106496
    | exact resolve eq106496 eq105725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105725 eq106496
  have eq112983 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq112982
  have eq112984 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq112983
  have eq113004 : (τ (σ x)) = (k y (τ (σ x))) := by
    first
    | (have i₁ := eq113 y
       have i₂ := eq112984
       grind)
    | exact superpose eq112984 eq113
    | exact resolve eq113 eq112984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq113106 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq407 (σ y) (σ y)
       have i₂ := eq112984
       grind)
    | exact superpose eq112984 eq407
    | exact resolve eq407 eq112984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112984
  have eq113375 : x = (k y x) := by
    first
    | (have i₁ := eq113004
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq113004
    | exact resolve eq113004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113004
  have eq113798 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq6160 x y
       have i₂ := eq113375
       grind)
    | exact superpose eq113375 eq6160
    | (have j0 := eq6160 x y
       grind)
    | exact resolve eq6160 eq113375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6160 eq113375
  have eq116178 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq113106
       grind)
    | exact superpose eq113106 eq16
    | exact resolve eq16 eq113106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113106
  have eq119091 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq116178
       have i₂ := eq113798
       grind)
    | exact superpose eq113798 eq116178
    | exact resolve eq116178 eq113798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113798
  have eq119252 : x = (M.op y y) := by grind
  clear eq119091
  have eq119803 : x = (M.op x y) := by
    first
    | (have i₁ := eq407 y y
       have i₂ := eq119252
       grind)
    | exact superpose eq119252 eq407
    | exact resolve eq407 eq119252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq119252
  have eq121255 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq116178
       have i₂ := eq119803
       grind)
    | exact superpose eq119803 eq116178
    | exact resolve eq116178 eq119803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116178 eq119803
  have eq121416 : False := by grind
  exact eq121416

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq36 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
  have eq37 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq43 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq25
    | exact resolve eq25 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq40
  have eq44 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq43
       have i₂ := eq42
       grind)
    | exact superpose eq42 eq43
    | exact resolve eq43 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq43
  have eq48 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq49 : ∀ X0 X1 : G, (M.op (M.op X1 (k X0 X0)) (k X0 X0)) = X0 := by
    intro X0 X1
    grind
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (k (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35 (M.op X2 (M.op X0 X3)) X1 (k X0 X0)
       have i₂ := eq35 X0 X2 X3
       grind)
    | exact superpose eq35 eq35
    | exact resolve eq35 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op X0 (M.op x y)) (k (τ (σ x)) (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq44 eq35
    | exact resolve eq35 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (k X0 X0)) = X0 := by
    intro X0 X1
    grind
  have eq56 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (τ X0) X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq48
    | exact resolve eq48 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq80 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq80
  have eq98 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq44 eq14
    | (have j0 := eq14 (M.op x y) (k (τ (σ y)) (τ (σ x)))
       grind)
    | exact resolve eq14 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X1) X2) (k X0 X0)) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X0 X2 X1
       have i₂ := eq14 (M.op X0 X1) X2
       grind)
    | exact superpose eq14 eq35
    | (have j1 := eq14 (M.op X0 X1) X2
       grind)
    | exact resolve eq35 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op X2 (M.op X0 X1)) ∨ (M.op (k (M.op X0 X1) X2) (k X0 X0)) = X0 ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    grind
  clear eq103
  have eq118 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq100
  have eq120 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq98
  have eq168 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (τ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq56
    | exact resolve eq56 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq207 : ∀ X0 : G, (M.op (k (k X0 X0) (k X0 X0)) (k X0 X0)) = X0 := by
    intro X0
    grind
  have eq211 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 (M.op x (k X0 X0))
       have i₂ := eq49 X0 x
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : (τ (σ x)) = (M.op (k (M.op x y) (M.op x y)) (k (τ (σ x)) (τ (σ x)))) := by grind
  clear eq51
  have eq262 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (k X0 X0) (k (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X1 (M.op X0 X2)) (k X0 X0)
       have i₂ := eq35 X0 X1 X2
       grind)
    | exact superpose eq35 eq54
    | exact resolve eq54 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 X2 : G, (k (M.op X0 X2) (M.op X0 X2)) = (M.op (M.op X1 X0) (k (k (M.op X0 X2) (M.op X0 X2)) (k (M.op X0 X2) (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 (k (M.op X0 X2) (M.op X0 X2)) X1 (k X0 X0)
       have i₂ := eq54 X0 X2
       grind)
    | exact superpose eq54 eq35
    | exact resolve eq35 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : (k (M.op x y) (M.op x y)) = (M.op (k (τ (σ x)) (τ (σ x))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq247 eq54
    | exact resolve eq54 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (τ (σ x))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq247 eq35
    | exact resolve eq35 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq324 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq118 eq34
    | exact resolve eq34 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33 eq84
    | (have j0 := eq84 (σ y) (σ x)
       grind)
    | exact resolve eq84 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 : G, (M.op X1 (τ (σ x))) = (M.op (M.op X0 (k (M.op x y) (M.op x y))) (k (M.op X1 (τ (σ x))) (M.op X1 (τ (σ x))))) := by
    intro X0 X1
    first
    | exact superpose eq286 eq35
    | exact resolve eq35 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq567 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 (k X0 X0))) (k (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X1 (k X0 X0)) X1 X2 (k X0 X0)
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq50
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (k (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq35 (M.op X4 X1) X3 (k (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq50 X1 X4 X0 X2
       grind)
    | exact superpose eq50 eq35
    | exact resolve eq35 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq50
  have eq615 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq120 eq15
    | exact resolve eq15 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq616 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq615
       have i₂ := eq37 sF5
       grind)
    | exact superpose eq37 eq615
    | exact resolve eq615 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq617 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq27 eq616
    | exact resolve eq616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq637 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq617 eq15
    | exact resolve eq15 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq637
       have i₂ := eq37 sF4
       grind)
    | exact superpose eq37 eq637
    | exact resolve eq637 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq640 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq639
       have i₂ := eq37 sF5
       grind)
    | exact superpose eq37 eq639
    | exact resolve eq639 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq641 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq27 eq640
    | exact resolve eq640 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq642 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq641 eq38
    | exact resolve eq38 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq660 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq642
       have i₂ := eq168 sF5 sF5
       grind)
    | exact superpose eq168 eq642
    | exact resolve eq642 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq695 : ∀ X0 X1 X2 : G, (M.op (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) (k X2 X2)) = X2 ∨ (M.op (k (M.op X0 X1) X2) (k X0 X0)) = X0 ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X0 X1)
       have i₂ := eq115 X0 X1 X2
       grind)
    | exact superpose eq115 eq54
    | (have j1 := eq115 X0 X1 X2
       grind)
    | exact resolve eq54 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq712 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq660 eq49
    | exact resolve eq49 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq660
  have eq832 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 X0 (k X0 X0)
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq54
    | exact resolve eq54 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq836 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    grind
  clear eq832
  have eq1009 : ∀ X0 : G, (M.op X0 (τ (σ x))) = (M.op (M.op x y) (k (M.op X0 (τ (σ x))) (M.op X0 (τ (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq527 (k (k sF2 sF2) (k sF2 sF2)) x
       have i₂ := eq207 sF2
       grind)
    | exact superpose eq207 eq527
    | exact resolve eq527 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq1059 : (k (τ (σ x)) (τ (σ x))) = (M.op (M.op x y) (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x))))) := by grind
  clear eq1009
  have eq1075 : (k (τ (σ x)) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) := by
    first
    | (have i₁ := eq1059
       have i₂ := eq836 (τ sF4)
       grind)
    | exact superpose eq836 eq1059
    | exact resolve eq1059 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1088 : (k (τ (σ x)) (τ (σ x))) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (k (M.op x y) (M.op x y)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq1075 eq84
    | (have j0 := eq84 (τ (σ x)) (M.op x y)
       grind)
    | (have r₁ := eq84 (τ (σ x)) (M.op x y)
       have r₂ := eq1075
       grind)
    | exact resolve eq84 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq1075
  have eq1091 : (k (M.op x y) (M.op x y)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq1088
  have eq1168 : (σ (k (M.op x y) (M.op x y))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq1091 eq15
    | exact resolve eq15 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1170 : (σ (k (M.op x y) (M.op x y))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq27 eq1168
    | exact resolve eq1168 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1172 : (σ (k (M.op x y) (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq1170
       have i₂ := eq37 sF4
       grind)
    | exact superpose eq37 eq1170
    | exact resolve eq1170 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1173 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq1172
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1172
    | exact resolve eq1172 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1174 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq27 eq1173
    | exact resolve eq1173 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1188 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ x) (σ (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq1174 eq211
    | exact resolve eq211 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1201 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq118 eq368
    | (have r₁ := eq368
       have r₂ := eq118
       grind)
    | exact resolve eq368 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq368
  have eq1202 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1201
  have eq1203 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1202
  have eq1594 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X1 (M.op X2 (k X0 X0))) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1 X2
    grind
  have eq1620 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 (k (τ (σ y)) (τ (σ y))))) (k (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq44 eq567
    | exact resolve eq567 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1626 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op X1 (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq284 eq567
    | exact resolve eq567 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq567
  have eq1667 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op X1 (k (M.op x y) (M.op x y)))) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1626 X0 X1
       have i₂ := eq836 sF2
       grind)
    | exact superpose eq836 eq1626
    | exact resolve eq1626 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq1692 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X1 (M.op X2 (k X0 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1594 X0 X1 X2
       have i₂ := eq836 X0
       grind)
    | exact superpose eq836 eq1594
    | exact resolve eq1594 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1711 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1667 X0 (k (k sF2 sF2) (k sF2 sF2))
       have i₂ := eq207 sF2
       grind)
    | exact superpose eq207 eq1667
    | exact resolve eq1667 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq1755 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1711 eq712
    | exact resolve eq712 eq1711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq1711
  have eq1865 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 (M.op (τ (σ y)) X2))) (k (M.op x y) (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq44 eq582
    | exact resolve eq582 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq2212 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (k (k (M.op X0 X2) (M.op X0 X2)) (k (M.op X0 X2) (M.op X0 X2))) (k (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262 (k (M.op X0 X1) (M.op X0 X1)) X1 (k X0 X0)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq262
    | exact resolve eq262 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq2272 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X0 X2) (k (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2212 X0 X1 X2
       have i₂ := eq836 (M.op X0 X2)
       grind)
    | exact superpose eq836 eq2212
    | exact resolve eq2212 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212
  have eq3407 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 (τ (σ y)))) (k (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1865 X0 X1 (k (τ sF5) (τ sF5))
       have i₂ := eq211 (τ sF5)
       grind)
    | exact superpose eq211 eq1865
    | exact resolve eq1865 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq3455 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (k (τ (σ y)) (τ (σ y)))) (k (M.op x y) (M.op x y))) := by
    intro X0
    grind
  clear eq3407
  have eq3584 : (M.op x y) = (M.op (τ (σ y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq3455 (k (k (τ sF5) (τ sF5)) (k (τ sF5) (τ sF5)))
       have i₂ := eq207 (τ sF5)
       grind)
    | exact superpose eq207 eq3455
    | exact resolve eq3455 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq3455
  have eq3640 : (τ (σ y)) = (M.op (k (M.op x y) (M.op x y)) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | exact superpose eq3584 eq54
    | exact resolve eq54 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3584
  have eq3768 : (k (M.op x y) (M.op x y)) = (M.op (k (τ (σ y)) (τ (σ y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq3640 eq54
    | exact resolve eq54 eq3640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3787 : (k (M.op x y) (M.op x y)) = (M.op (k (τ (σ y)) (τ (σ y))) (M.op x y)) := by
    first
    | (have i₁ := eq3768
       have i₂ := eq836 sF2
       grind)
    | exact superpose eq836 eq3768
    | exact resolve eq3768 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3768
  have eq4016 : (k (τ (σ y)) (τ (σ y))) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | exact superpose eq3787 eq54
    | exact resolve eq54 eq3787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3787
  have eq4039 : (k (τ (σ y)) (τ (σ y))) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ y))) := by
    first
    | (have i₁ := eq4016
       have i₂ := eq836 (τ sF5)
       grind)
    | exact superpose eq836 eq4016
    | exact resolve eq4016 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016
  have eq4047 : (k (τ (σ y)) (τ (σ y))) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq4039
       have i₂ := eq836 sF2
       grind)
    | exact superpose eq836 eq4039
    | exact resolve eq4039 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4039
  have eq4465 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1 (k X0 X0)
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq274
    | exact resolve eq274 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq4656 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4465 X0 X1
       have i₂ := eq836 X0
       grind)
    | exact superpose eq836 eq4465
    | exact resolve eq4465 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4465
  have eq6678 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (τ (σ y))) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3640 eq1620
    | exact resolve eq1620 eq3640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620 eq3640
  have eq6839 : (M.op x y) = (M.op (k (τ (σ y)) (τ (σ y))) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq4047 eq6678
    | exact resolve eq6678 eq4047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6678
  have eq6916 : (k (τ (σ y)) (τ (σ y))) = (M.op (k (M.op x y) (M.op x y)) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | exact superpose eq6839 eq54
    | exact resolve eq54 eq6839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq6839
  have eq6949 : (k (τ (σ y)) (τ (σ y))) = (M.op (k (M.op x y) (M.op x y)) (τ (σ y))) := by
    first
    | (have i₁ := eq6916
       have i₂ := eq836 (τ sF5)
       grind)
    | exact superpose eq836 eq6916
    | exact resolve eq6916 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6916
  have eq8748 : ∀ X0 X1 : G, (M.op (k (k X0 X0) (k X0 X0)) (k X1 X1)) = X1 ∨ (M.op (k X0 X1) (k X0 X0)) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 (k X0 X0) x
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq695
    | (have j0 := eq695 (k (k X0 X0) (k X0 X0)) (k X1 X1) X1
       grind)
    | exact resolve eq695 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq9073 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X0)) = X0 ∨ (M.op X0 (k X1 X1)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8748 X0 X1
       have i₂ := eq836 X0
       grind)
    | exact superpose eq836 eq8748
    | (have j0 := eq8748 X0 X1
       grind)
    | exact resolve eq8748 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8748
  have eq26378 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1755 eq37
    | exact resolve eq37 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq26382 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq26378
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq26378
    | exact resolve eq26378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26378
  have eq26400 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq27 eq26382
    | exact resolve eq26382 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26382
  have eq26446 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq26400 eq211
    | exact resolve eq211 eq26400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26511 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26400 eq1692
    | exact resolve eq1692 eq26400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692 eq26400
  have eq31754 : (k (τ (σ y)) (τ (σ x))) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1203 eq168
    | exact resolve eq168 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq31785 : (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq31754
       have i₂ := eq168 sF4 sF4
       grind)
    | exact superpose eq168 eq31754
    | exact resolve eq31754 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq31754
  have eq34071 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (k (σ x) (σ (M.op x y))) X0) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq1188 eq2272
    | exact resolve eq2272 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188 eq2272
  have eq58879 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq34071 (k sF4 sF4)
       have i₂ := eq9073 sF4 sF3
       grind)
    | exact superpose eq9073 eq34071
    | (have j1 := eq9073 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq34071 eq9073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9073 eq34071
  have eq59019 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq58879
  have eq418898 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq31785 eq617
    | exact resolve eq617 eq31785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq31785
  have eq418909 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq418898
       have r₂ := eq324
       grind)
    | exact resolve eq418898 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418898
  have eq764909 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq418909 eq836
    | exact resolve eq836 eq418909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418909
  have eq765822 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq764909 eq44
    | exact resolve eq44 eq764909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764909
  have eq765828 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq6949 eq765822
    | exact resolve eq765822 eq6949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6949 eq765822
  have eq794511 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq765828 eq15
    | exact resolve eq15 eq765828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765828
  have eq794513 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq794511
       have i₂ := eq37 sF5
       grind)
    | exact superpose eq37 eq794511
    | exact resolve eq794511 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794511
  have eq794531 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq794513
    | exact resolve eq794513 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794513
  have eq794532 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have r₁ := eq794531
       have r₂ := eq324
       grind)
    | exact resolve eq794531 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq794531
  have eq794534 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq794532 eq34
    | exact resolve eq34 eq794532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794532
  have eq795316 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq26446 eq794534
    | (have r₁ := eq794534
       have r₂ := eq26446
       grind)
    | exact resolve eq794534 eq26446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26446
  have eq795319 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq795316
  have eq795320 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq795319
  have eq795347 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq795320 eq26511
    | exact resolve eq26511 eq795320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26511 eq795320
  have eq795427 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq795347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795347
  have eq795437 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq795427 X0
       grind)
    | (have r₁ := eq795427 X0
       have r₂ := eq794534
       grind)
    | exact resolve eq795427 eq794534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794534 eq795427
  have eq795441 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq795437 x
       have i₂ := eq4656 sF3 x
       grind)
    | exact superpose eq4656 eq795437
    | exact resolve eq795437 eq4656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4656 eq795437
  have eq798256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq795441 eq59019
    | exact resolve eq59019 eq795441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59019 eq795441
  have eq798443 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33 eq798256
    | exact resolve eq798256 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798256
  have eq798457 : (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq798443
       have r₂ := eq34
       grind)
    | exact resolve eq798443 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798443
  have eq817251 : (σ y) = (σ (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq798457 eq37
    | exact resolve eq37 eq798457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798457
  have eq817267 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq817251
       have i₂ := eq37 sF4
       grind)
    | exact superpose eq37 eq817251
    | exact resolve eq817251 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817251
  have eq817268 : (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq817267
  have eq819911 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq817268 eq37
    | exact resolve eq37 eq817268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817268
  have eq819919 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq819911
    | exact resolve eq819911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819911
  have eq819920 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq819919
  have eq819935 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq819920 eq33
    | exact resolve eq33 eq819920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819936 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq819920 eq44
    | exact resolve eq44 eq819920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819920
  have eq820798 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq819936
  have eq820799 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq819935
  have eq823208 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq820799 eq34
    | exact resolve eq34 eq820799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820799
  have eq826129 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq820798 eq15
    | exact resolve eq15 eq820798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820798
  have eq826132 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq826129
       have i₂ := eq37 sF4
       grind)
    | exact superpose eq37 eq826129
    | exact resolve eq826129 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826129
  have eq826150 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq826132
    | exact resolve eq826132 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq826132
  have eq826151 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq826150
       have r₂ := eq823208
       grind)
    | exact resolve eq826150 eq823208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823208 eq826150
  have eq826158 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq826151 eq38
    | exact resolve eq38 eq826151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq829194 : (M.op x y) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq826158 eq44
    | exact resolve eq44 eq826158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq829287 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq826158 eq37
    | exact resolve eq37 eq826158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826158
  have eq830398 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq829194 eq4047
    | exact resolve eq4047 eq829194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047 eq829194
  have eq830670 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) := by
    first
    | exact superpose eq830398 eq15
    | exact resolve eq15 eq830398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830398
  have eq830673 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq830670
       have i₂ := eq37 sF5
       grind)
    | exact superpose eq37 eq830670
    | exact resolve eq830670 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq830670
  have eq830713 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq829287 eq830673
    | exact resolve eq830673 eq829287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829287 eq830673
  have eq832625 : (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq830713 eq836
    | exact resolve eq836 eq830713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq830713
  have eq834712 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq832625 eq211
    | exact resolve eq211 eq832625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq832625
  have eq836152 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq834712 eq33
    | exact resolve eq33 eq834712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq834712
  have eq838892 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq836152 eq34
    | exact resolve eq34 eq836152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq836152
  have eq839576 : False := by grind
  exact eq839576

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq79 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq26
    | exact resolve eq26 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq202 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq193 x y
       grind)
    | exact superpose eq193 eq16
    | (have j1 := eq193 x y
       grind)
    | exact resolve eq16 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq925 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq202
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq202
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq202
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq202
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq202 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq926 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq925
  have eq22237 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq926
       grind)
    | exact superpose eq926 eq16
    | exact resolve eq16 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq22238 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq22237
       have r₂ := eq23 x
       grind)
    | exact resolve eq22237 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22237
  have eq142854 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22238
       grind)
    | exact superpose eq22238 eq10
    | exact resolve eq10 eq22238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22238
  have eq142990 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq142854
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq142854
    | exact resolve eq142854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142854
  have eq144119 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq142990
       grind)
    | exact superpose eq142990 eq16
    | exact resolve eq16 eq142990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142990
  have eq144120 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq144119
       have r₂ := eq23 x
       grind)
    | exact resolve eq144119 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq144119
  have eq144222 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq144120
       grind)
    | exact superpose eq144120 eq10
    | exact resolve eq10 eq144120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144120
  have eq144411 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq144222
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq144222
    | exact resolve eq144222 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144222
  have eq144412 : y = (M.op x x) := by grind
  clear eq144411
  have eq145392 : x = (M.op x y) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq144412
       grind)
    | exact superpose eq144412 eq26
    | exact resolve eq26 eq144412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq145399 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq79 x
       have i₂ := eq144412
       grind)
    | exact superpose eq144412 eq79
    | exact resolve eq79 eq144412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq144412
  have eq167459 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq145399
       grind)
    | exact superpose eq145399 eq16
    | exact resolve eq16 eq145399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145399
  have eq167699 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq167459
       have i₂ := eq145392
       grind)
    | exact superpose eq145392 eq167459
    | exact resolve eq167459 eq145392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145392 eq167459
  have eq167700 : False := by grind
  exact eq167700

/-- `Equation1912`: `x = (y ◇ (x ◇ z)) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pyx_x_pxy_Equation1912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X2 X0)) = X0 := by
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
  have eq177 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq16 X2 (M.op x (M.op X0 X2)) X0
       have i₂ := eq16 X0 x X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 (M.op X1 (M.op X0 X2)) (M.op X2 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X2 X0)
       have i₂ := eq177 X2 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ y) (σ x))))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq381 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq465 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq381 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq381
    | exact resolve eq381 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq612 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X0 X0))) (k X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k X0 (M.op X0 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq177 X0 X0
       grind)
    | (have i₁ := eq613 X0 X1
       have i₂ := eq177 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq177 eq613
    | exact resolve eq613 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq628 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 X1
       have i₂ := eq177 X0 X0
       grind)
    | (have i₁ := eq612 X0 X1
       have i₂ := eq177 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq177 eq612
    | exact resolve eq612 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq629 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X1 X2 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq182
    | exact resolve eq182 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (k X0 (M.op X0 X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (M.op X0 X0) X1 X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 : G, (M.op (M.op X1 (k X0 (M.op X0 X0))) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 X1
       have i₂ := eq177 X0 X0
       grind)
    | (have i₁ := eq630 X0 X1
       have i₂ := eq177 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq177 eq630
    | exact resolve eq630 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq712 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) (k X0 X1)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq744 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq750 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq774 : ∀ X0 X1 : G, (M.op (k X0 (M.op X0 X0)) (M.op (M.op X1 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 (M.op X0 X0) X1
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq187
    | exact resolve eq187 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq187 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq187
    | (have j0 := eq187 y x X0
       grind)
    | exact resolve eq187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 : G, (M.op y (M.op (M.op X0 (M.op x y)) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq183 eq187
    | exact resolve eq187 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq187
    | (have j0 := eq187 (σ y) (σ x) X0
       grind)
    | exact resolve eq187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq855 : y = (M.op (M.op x y) (k y (M.op y y))) := by
    first
    | (have i₁ := eq790 y
       have i₂ := eq181 y
       grind)
    | exact superpose eq181 eq790
    | exact resolve eq790 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq790 eq177
    | exact resolve eq177 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq899 : ∀ X0 : G, (M.op y X0) = (M.op (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq791 eq177
    | exact resolve eq177 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq923 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq792 sF3
       have i₂ := eq181 sF3
       grind)
    | exact superpose eq181 eq792
    | exact resolve eq792 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq933 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq792 eq177
    | exact resolve eq177 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq992 : (k y (M.op y y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq855 eq177
    | exact resolve eq177 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq1021 : ∀ X0 X1 : G, (M.op (M.op X1 y) (M.op (M.op x y) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq187 y X1 X0
       have i₂ := eq865 X0
       grind)
    | (have i₁ := eq187 y X1 x
       have i₂ := eq865 x
       grind)
    | exact superpose eq865 eq187
    | exact resolve eq187 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq1100 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op (M.op X1 (M.op y X0)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq899 eq182
    | exact resolve eq182 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq899
  have eq1122 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X1 (M.op y X0)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1100 X0 X1
       have i₂ := eq177 X0 sF0
       grind)
    | (have i₁ := eq1100 X0 X1
       have i₂ := eq177 X0 (M.op X0 (M.op X0 sF0))
       grind)
    | exact superpose eq177 eq1100
    | exact resolve eq1100 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1134 : (k (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq923 eq177
    | exact resolve eq177 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq1165 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq933 eq187
    | exact resolve eq187 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq1280 : (k (σ y) (σ (M.op y y))) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq36
    | exact resolve eq36 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq992
  have eq1307 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | exact superpose eq1021 eq177
    | exact resolve eq177 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1441 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq1165 eq177
    | exact resolve eq177 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq2156 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq629 X1 X2 X3
       have i₂ := eq629 X1 X2 X0
       grind)
    | (have i₁ := eq629 X0 X1 X2
       have i₂ := eq629 X0 X1 X1
       grind)
    | exact superpose eq629 eq629
    | exact resolve eq629 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2188 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op (k X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1 (M.op X0 X0)
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq629
    | exact resolve eq629 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2303 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 (M.op X2 X1) X2
       have i₂ := eq629 X1 X2 X0
       grind)
    | (have i₁ := eq177 (M.op X2 X0) X1
       have i₂ := eq629 X0 X1 X2
       grind)
    | exact superpose eq629 eq177
    | exact resolve eq177 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq3220 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2156 X1 (M.op X2 X0) X3 (M.op x (M.op X0 X2))
       have i₂ := eq16 X0 x X2
       grind)
    | exact superpose eq16 eq2156
    | exact resolve eq2156 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156
  have eq5222 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq40
    | exact resolve eq40 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq5223 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5222
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5222
    | exact resolve eq5222 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5222
  have eq5225 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq5223
    | exact resolve eq5223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5223
  have eq15776 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq712 X0 X0 (M.op x (k X0 (M.op X0 X0)))
       have i₂ := eq667 X0 x
       grind)
    | exact superpose eq667 eq712
    | (have j0 := eq712 X0 X0 x
       grind)
    | exact resolve eq712 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq712
  have eq15816 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15776 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15776
  have eq15906 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0 (k X0 X0)
       have i₂ := eq15816 X0
       grind)
    | exact superpose eq15816 eq177
    | (have j1 := eq15816 X0
       grind)
    | exact resolve eq177 eq15816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15816
  have eq16026 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15906 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq15906 X0
       have r₂ := eq13 X0 (k X0 X0)
       grind)
    | (have r₁ := eq15906 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq15906 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq15906 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15906
  have eq16128 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 (k X0 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 X1
       have i₂ := eq16026 X0
       grind)
    | exact superpose eq16026 eq627
    | exact resolve eq627 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq16129 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq16026 X0
       grind)
    | exact superpose eq16026 eq628
    | exact resolve eq628 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq16138 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0 X0
       have i₂ := eq16026 X0
       grind)
    | exact superpose eq16026 eq177
    | exact resolve eq177 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq16185 : ∀ X0 : G, (M.op x y) = (M.op (k (M.op y X0) (M.op y X0)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1122 X0 (M.op y X0)
       have i₂ := eq16026 (M.op y X0)
       grind)
    | exact superpose eq16026 eq1122
    | exact resolve eq1122 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq16222 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (k y y) X0) := by
    intro X0
    first
    | (have i₁ := eq1307 X0 y
       have i₂ := eq16026 y
       grind)
    | exact superpose eq16026 eq1307
    | exact resolve eq1307 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq16279 : (σ (M.op (M.op x y) y)) = (k (σ y) (σ (k y y))) := by
    first
    | (have i₁ := eq1280
       have i₂ := eq16026 y
       grind)
    | exact superpose eq16026 eq1280
    | exact resolve eq1280 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq16306 : (k (σ y) (k (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq1134
       have i₂ := eq16026 sF3
       grind)
    | exact superpose eq16026 eq1134
    | exact resolve eq1134 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq16346 : (σ (M.op (M.op x y) y)) = (k (σ y) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16279
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq16279
    | exact resolve eq16279 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq16279
  have eq16426 : (k (σ y) (k (σ y) (σ y))) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq16346
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16346
    | exact resolve eq16346 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16346
  have eq16433 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq16306 eq16426
    | exact resolve eq16426 eq16306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16306 eq16426
  have eq16434 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16138 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16138
    | exact resolve eq16138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16435 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16138 (τ X0)
       have i₂ := eq465 X0 X0
       grind)
    | exact superpose eq465 eq16138
    | exact resolve eq16138 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq18597 : ∀ X0 X1 : G, (M.op (M.op X1 (k X0 (k X0 X0))) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2303 (M.op x X0) (k X0 (k X0 X0)) X1
       have i₂ := eq16129 X0 x
       grind)
    | exact superpose eq16129 eq2303
    | exact resolve eq2303 eq16129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2303 eq16129
  have eq132590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5225 eq750
    | exact resolve eq750 eq5225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq5225
  have eq132603 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq132590
       have r₂ := eq27
       grind)
    | exact resolve eq132590 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132590
  have eq132612 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq132603
       have i₂ := eq16026 sF2
       grind)
    | exact superpose eq16026 eq132603
    | exact resolve eq132603 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132603
  have eq132619 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq132612
       have i₂ := eq16026 x
       grind)
    | exact superpose eq16026 eq132612
    | exact resolve eq132612 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16026 eq132612
  have eq133413 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq132619 eq97
    | exact resolve eq97 eq132619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq132619
  have eq133513 : y = (k x x) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq133413
    | exact resolve eq133413 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133413
  have eq133514 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq133513
  have eq133616 : (σ x) = (M.op (M.op (σ x) (k (σ y) (k (σ y) (σ y)))) (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq133514 eq18597
    | exact resolve eq18597 eq133514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133514
  have eq133635 : (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq133616
       have i₂ := eq16128 sF3 sF2
       grind)
    | exact superpose eq16128 eq133616
    | exact resolve eq133616 eq16128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133616
  have eq134136 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq133635 eq16435
    | exact resolve eq16435 eq133635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16435 eq133635
  have eq134197 : (τ (σ y)) = (M.op (τ (σ y)) x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq134136
    | exact resolve eq134136 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq134136
  have eq134242 : y = (M.op y x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq134197
    | exact resolve eq134197 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq134197
  have eq134243 : y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq134242
  have eq134280 : x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16138 x
       have i₂ := eq134243
       grind)
    | exact superpose eq134243 eq16138
    | exact resolve eq16138 eq134243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16138 eq134243
  have eq134368 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134280
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq134280
    | exact resolve eq134280 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134280
  have eq134454 : (M.op x y) = (M.op (k y y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16185 x
       have i₂ := eq134368
       grind)
    | exact superpose eq134368 eq16185
    | exact resolve eq16185 eq134368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16185
  have eq134505 : x = (M.op (M.op x (k y (k y y))) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18597 y x
       have i₂ := eq134368
       grind)
    | exact superpose eq134368 eq18597
    | exact resolve eq18597 eq134368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18597 eq134368
  have eq134524 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134505
       have i₂ := eq16128 y x
       grind)
    | exact superpose eq16128 eq134505
    | exact resolve eq134505 eq16128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16128 eq134505
  have eq134567 : (M.op x y) = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134454
       have i₂ := eq16222 (M.op x sF0)
       grind)
    | exact superpose eq16222 eq134454
    | exact resolve eq134454 eq16222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16222 eq134454
  have eq134607 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq183 eq134567
    | exact resolve eq134567 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq134567
  have eq134893 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16434 y
       have i₂ := eq134524
       grind)
    | exact superpose eq134524 eq16434
    | exact resolve eq16434 eq134524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16434 eq134524
  have eq134962 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134893
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq134893
    | exact resolve eq134893 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134893
  have eq135003 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134962
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq134962
    | exact resolve eq134962 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq134962
  have eq135045 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq134607 eq16433
    | exact resolve eq16433 eq134607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134607
  have eq135175 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq135045
    | exact resolve eq135045 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135045
  have eq135981 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq135003 eq217
    | exact resolve eq217 eq135003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq135003
  have eq136125 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X1 (σ y)) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq135981 X1 X1
       have i₂ := eq3220 (M.op X1 sF3) X1 sF4 sF3
       grind)
    | exact superpose eq3220 eq135981
    | exact resolve eq135981 eq3220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3220 eq135981
  have eq136158 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1441 eq136125
    | (have j0 := eq136125 (σ x)
       grind)
    | exact resolve eq136125 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441 eq136125
  have eq136171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq135175 eq136158
    | exact resolve eq136158 eq135175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135175 eq136158
  have eq136177 : x = (M.op x y) := by
    first
    | (have r₁ := eq136171
       have r₂ := eq27
       grind)
    | exact resolve eq136171 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136171
  have eq136182 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq136177
       grind)
    | exact superpose eq136177 eq18
    | exact resolve eq18 eq136177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq136183 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq136177
       grind)
    | exact superpose eq136177 eq22
    | exact resolve eq22 eq136177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq136177
  have eq136256 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq136183 eq20
    | exact resolve eq20 eq136183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136183
  have eq136863 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq136182 eq16433
    | exact resolve eq16433 eq136182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16433 eq136182
  have eq136993 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq20 eq136863
    | exact resolve eq136863 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq136863
  have eq137020 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq136256 eq136993
    | exact resolve eq136993 eq136256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136993
  have eq137321 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (M.op (σ y) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq137020 eq774
    | exact resolve eq774 eq137020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq137392 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (M.op (σ y) (σ y))) (σ y)) := by
    first
    | exact superpose eq184 eq137321
    | exact resolve eq137321 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq137321
  have eq137454 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq137392
       have i₂ := eq2188 sF3 sF3
       grind)
    | exact superpose eq2188 eq137392
    | exact resolve eq137392 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188 eq137392
  have eq137470 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq933 eq137454
    | exact resolve eq137454 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933 eq137454
  have eq137475 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq137020 eq137470
    | exact resolve eq137470 eq137020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137020 eq137470
  have eq137478 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq137475 eq27
    | exact resolve eq27 eq137475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq137475
  have eq137776 : False := by grind
  exact eq137776

/-- `Equation1921`: `x = (y ◇ (y ◇ x)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation1921 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1921 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1921.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq515 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
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
  have eq12089 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq515 X0 X1
       grind)
    | exact superpose eq515 eq12
    | (have j0 := eq12 (τ X0) X1
       have j1 := eq515 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq515 X0 X1
       grind)
    | exact resolve eq12 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq12120 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq12089 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12089
  have eq16643 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq12120 X0 X1
       grind)
    | exact superpose eq12120 eq10
    | (have j1 := eq12120 X0 X1
       grind)
    | exact resolve eq10 eq12120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12120
  have eq16740 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16643 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq16643
    | (have j0 := eq16643 X0 X1
       grind)
    | exact resolve eq16643 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16643
  have eq16741 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq16740 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16740
  have eq16762 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16741 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16741
    | exact resolve eq16741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16798 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq16741 X0 X1
       grind)
    | exact superpose eq16741 eq17
    | (have j1 := eq16741 X0 X1
       grind)
    | exact resolve eq17 eq16741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq16741
  have eq17030 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq16762 (σ X0) (σ X1)
       grind)
    | exact superpose eq16762 eq15
    | (have j1 := eq16762 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq16762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16762
  have eq17124 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16798 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16798
    | exact resolve eq16798 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq17275 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17124 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq17124
    | (have j0 := eq17124 X0 X1
       grind)
    | exact resolve eq17124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17124
  have eq22523 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17030 x y
       grind)
    | exact superpose eq17030 eq16
    | (have j1 := eq17030 x y
       grind)
    | exact resolve eq16 eq17030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17030
  have eq22620 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq22523
       have i₂ := eq17275 x y
       grind)
    | exact superpose eq17275 eq22523
    | (have j1 := eq17275 (σ y) (σ x)
       grind)
    | (have r₁ := eq22523
       have r₂ := eq17275 x y
       grind)
    | exact resolve eq22523 eq17275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22623 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq22620
  have eq22636 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq22623
       grind)
    | exact superpose eq22623 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq22623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22637 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq22623
       grind)
    | exact superpose eq22623 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq22623
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22623
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22623
       grind)
    | exact resolve eq13 eq22623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22623
  have eq22643 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq22637
  have eq22644 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq22636
       have r₂ := eq22643
       grind)
    | exact resolve eq22636 eq22643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22636 eq22643
  have eq22645 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq22523
       have i₂ := eq22644
       grind)
    | exact superpose eq22644 eq22523
    | exact resolve eq22523 eq22644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22523 eq22644
  have eq22649 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq22645
  have eq22650 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq22649
  have eq22666 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq22650
       grind)
    | exact superpose eq22650 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq22650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22667 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq22650
       grind)
    | exact superpose eq22650 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22650
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq22650
       grind)
    | exact resolve eq13 eq22650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22650
  have eq22673 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq22667
  have eq22678 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22673
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22673
    | exact resolve eq22673 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22673
  have eq22679 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22666
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22666
    | exact resolve eq22666 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22666
  have eq22686 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq22679
       have r₂ := eq22678
       grind)
    | exact resolve eq22679 eq22678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22678 eq22679
  have eq22704 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22686
       grind)
    | exact superpose eq22686 eq16
    | exact resolve eq16 eq22686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22686
  have eq22803 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq22704
       have i₂ := eq17275 x y
       grind)
    | exact superpose eq17275 eq22704
    | (have j1 := eq17275 y x
       grind)
    | (have r₁ := eq22704
       have r₂ := eq17275 x y
       grind)
    | exact resolve eq22704 eq17275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17275
  have eq22806 : (M.op x y) = (M.op y x) := by grind
  clear eq22803
  have eq22820 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq22806
       grind)
    | exact superpose eq22806 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq22806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22821 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq22806
       grind)
    | exact superpose eq22806 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq22806
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22806
       grind)
    | exact resolve eq13 eq22806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22806
  have eq22827 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq22821
  have eq22828 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq22820
       have r₂ := eq22827
       grind)
    | exact resolve eq22820 eq22827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22820 eq22827
  have eq22829 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq22704
       have i₂ := eq22828
       grind)
    | exact superpose eq22828 eq22704
    | exact resolve eq22704 eq22828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22704 eq22828
  have eq22834 : False := by grind
  exact eq22834
