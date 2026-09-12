import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_pyy_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
    intro X0 X1 X2 X3
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
  have eq176 : ∀ X0 X1 X2 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X0)) X5) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq16 X1 X2 (M.op x (M.op x X5)) X5
       have i₂ := eq16 X0 x x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq16 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq16 X0 x x (M.op x X5)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq181 X1 X0
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 X1 X2
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op x y)) y) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq177 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq177
    | exact resolve eq177 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq256 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq178 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq454 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq1482 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 (M.op X0 X0) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq1524 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (k (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 X2 X1 X3
       have i₂ := eq1482 X0 X1
       grind)
    | exact superpose eq1482 eq176
    | exact resolve eq176 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1550 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X1 X2 (M.op X0 X0)
       have i₂ := eq1482 X0 (M.op X1 X1)
       grind)
    | exact superpose eq1482 eq180
    | exact resolve eq180 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1646 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) = (M.op (k (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq256 x (M.op x x) X3
       have i₂ := eq1524 X0 X1 (M.op x x) X2
       grind)
    | exact superpose eq1524 eq256
    | exact resolve eq256 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1647 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op x y)) y) = (M.op (k (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq255 x (M.op x x) X3
       have i₂ := eq1524 X0 X1 (M.op x x) X2
       grind)
    | exact superpose eq1524 eq255
    | exact resolve eq255 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq1524
  have eq1702 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq11
    | (have j0 := eq11 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1740 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq181
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1793 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq1794 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq1811 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1740 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1825 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702
  have eq2169 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (k X0 X0) X3) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 X2 X1 X3
       have i₂ := eq1825 X2 X0
       grind)
    | exact superpose eq1825 eq180
    | (have j1 := eq1825 X1 (M.op (k X0 X0) X3)
       grind)
    | exact resolve eq180 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2172 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X1 X2
       have i₂ := eq1825 X2 X0
       grind)
    | exact superpose eq1825 eq181
    | (have j1 := eq1825 X1 X0
       grind)
    | exact resolve eq181 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2224 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1825 X0 (σ X1)
       grind)
    | exact superpose eq1825 eq10
    | (have j1 := eq1825 X0 (σ (k X1 X1))
       grind)
    | exact resolve eq10 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2227 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1825 X0 (τ X1)
       grind)
    | exact superpose eq1825 eq34
    | (have j1 := eq1825 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq2231 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2227 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq2227
    | (have j0 := eq2227 X0 X1
       grind)
    | exact resolve eq2227 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq8899 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1793
       grind)
    | exact superpose eq1793 eq40
    | exact resolve eq40 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1793
  have eq8900 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8899
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8899
    | exact resolve eq8899 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8899
  have eq8902 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq8900
    | exact resolve eq8900 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8900
  have eq41114 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2169 X1 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41179 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41114 X2 X1 (k X1 X1)
       have i₂ := eq181 (k X1 X1) X0
       grind)
    | (have i₁ := eq41114 X2 X1 (k X1 X1)
       have i₂ := eq181 X0 (k X1 X1)
       grind)
    | exact superpose eq181 eq41114
    | (have j0 := eq41114 X2 X1 X2
       grind)
    | (have r₁ := eq41114 X0 (M.op X1 X1) (k (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq181 (k (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq41114 X0 (M.op X0 X0) (k (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq181 X0 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq41114 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41212 : ∀ X0 X1 X2 X3 : G, (k X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 ∨ (M.op X3 X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41114 X2 X1 (k X1 X1)
       have i₂ := eq2172 X0 (k X1 X1) X3
       grind)
    | exact superpose eq2172 eq41114
    | (have j0 := eq41114 X2 X1 X2
       have j1 := eq2172 X1 X1 X2
       grind)
    | (have r₁ := eq41114 X0 (k X0 X0) (k (k X0 X0) (k X0 X0))
       have r₂ := eq2172 X0 (k (k X0 X0) (k X0 X0)) X2
       grind)
    | (have r₁ := eq41114 X0 X0 (k X0 X0)
       have r₂ := eq2172 X0 X1 (k X0 X0)
       grind)
    | (have r₁ := eq41114 X0 (M.op X2 X2) X2
       have r₂ := eq2172 (M.op (k (M.op X2 X2) (M.op X2 X2)) X2) X1 X2
       grind)
    | exact resolve eq41114 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41114
  have eq49615 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2224 X1 (M.op X2 X2)
       have i₂ := eq1550 X2 X2 X0
       grind)
    | exact superpose eq1550 eq2224
    | (have j0 := eq2224 X1 (M.op X0 X0)
       grind)
    | exact resolve eq2224 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq2224
  have eq50501 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq2231 X0 (σ X1)
       grind)
    | exact superpose eq2231 eq10
    | (have j1 := eq2231 X0 (σ X1)
       grind)
    | exact resolve eq10 eq2231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq50676 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50501 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq50501
    | (have j0 := eq50501 X0 X1
       grind)
    | exact resolve eq50501 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50501
  have eq61731 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X2 ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50676 X0 X2
       have i₂ := eq50676 X1 X2
       grind)
    | exact superpose eq50676 eq50676
    | (have j0 := eq50676 X1 X2
       have j1 := eq50676 X1 X2
       grind)
    | exact resolve eq50676 eq50676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50676
  have eq62152 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq61731 X0 X1 X2
       have j1 := eq41179 X0 X2 X1
       grind)
    | (have r₁ := eq61731 X0 X0 X1
       have r₂ := eq41179 X0 X1 X2
       grind)
    | (have r₁ := eq61731 X0 X1 (M.op X0 X0)
       have r₂ := eq41179 X0 (M.op X1 X1) X2
       grind)
    | (have r₁ := eq61731 X0 X1 X1
       have r₂ := eq41179 X0 X1 X2
       grind)
    | exact resolve eq61731 eq41179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61731
  have eq66583 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X1 X1)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq62152 X0 X1 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66584 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq62152 X0 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62152
  have eq66587 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq66584 X0 x
       have j1 := eq49615 X0 X0 X0
       grind)
    | (have r₁ := eq66584 x X0
       have r₂ := eq49615 X0 x x
       grind)
    | (have r₁ := eq66584 x x
       have r₂ := eq49615 X0 x x
       grind)
    | exact resolve eq66584 eq49615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66584
  have eq66588 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq66583 X0 X1
       have j1 := eq49615 X0 X1 X0
       grind)
    | (have r₁ := eq66583 X0 X0
       have r₂ := eq49615 X0 X0 x
       grind)
    | (have r₁ := eq66583 X0 x
       have r₂ := eq49615 X0 x x
       grind)
    | exact resolve eq66583 eq49615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49615 eq66583
  have eq67301 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq66588 (k (M.op x x) x) X1
       have i₂ := eq1647 x x (k (M.op x x) x) X0
       grind)
    | exact superpose eq1647 eq66588
    | exact resolve eq66588 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq67302 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq66588 (k (M.op x x) x) X1
       have i₂ := eq1646 x x (k (M.op x x) x) X0
       grind)
    | exact superpose eq1646 eq66588
    | exact resolve eq66588 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq67599 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X1 X1)
       have i₂ := eq66588 X1 X0
       grind)
    | exact superpose eq66588 eq15
    | exact resolve eq15 eq66588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8902 eq1794
    | exact resolve eq1794 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794 eq8902
  have eq132467 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq132458
       have r₂ := eq27
       grind)
    | exact resolve eq132458 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132458
  have eq132474 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1825 eq132467
    | (have j1 := eq1825 (σ x) (σ x)
       grind)
    | exact resolve eq132467 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825 eq132467
  have eq132477 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1811 eq132474
    | (have j1 := eq1811 x x
       grind)
    | exact resolve eq132474 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811 eq132474
  have eq132484 : (τ (σ y)) = (k x x) ∨ (σ x) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq132477 eq97
    | exact resolve eq97 eq132477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq132477
  have eq132524 : y = (k x x) ∨ (σ x) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31 eq132484
    | exact resolve eq132484 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq132484
  have eq132540 : (σ x) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq41212 y y x x
       grind)
    | (have r₁ := eq132524
       have r₂ := eq41212 x y x x
       grind)
    | (have r₁ := eq132524
       have r₂ := eq41212 x (σ x) x x
       grind)
    | exact resolve eq132524 eq41212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41212 eq132524
  have eq132574 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (σ x) X1) ∨ x = (M.op X2 X2) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2169 x X0 X2 X1
       have i₂ := eq132540
       grind)
    | exact superpose eq132540 eq2169
    | (have j0 := eq2169 (M.op (σ x) X1) X1 X0 x
       grind)
    | exact resolve eq2169 eq132540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169
  have eq132606 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) X1) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq132574 X0 X1 x
       have j1 := eq41179 X0 (M.op (σ x) X1) X0
       grind)
    | (have r₁ := eq132574 X0 X1 x
       have r₂ := eq41179 X0 (M.op (σ x) X1) x
       grind)
    | (have r₁ := eq132574 X0 (σ x) x
       have r₂ := eq41179 (σ x) (M.op X0 X0) x
       grind)
    | (have r₁ := eq132574 X0 X1 X0
       have r₂ := eq41179 X0 x x
       grind)
    | exact resolve eq132574 eq41179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132574
  have eq132620 : ∀ X1 : G, (k x x) = (M.op (σ x) X1) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X1
    first
    | exact superpose eq2172 eq132606
    | (have j1 := eq2172 y X1 x
       grind)
    | exact resolve eq132606 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172 eq132606
  have eq132627 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X1
    first
    | exact superpose eq132540 eq132620
    | exact resolve eq132620 eq132540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132540 eq132620
  have eq132821 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq132627 eq67599
    | exact resolve eq67599 eq132627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67599 eq132627
  have eq133140 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq132821
    | exact resolve eq132821 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132821
  have eq133385 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq133140 x
       have j1 := eq41179 x y x
       grind)
    | (have r₁ := eq133140 x
       have r₂ := eq41179 x x x
       grind)
    | (have r₁ := eq133140 x
       have r₂ := eq41179 x y x
       grind)
    | (have r₁ := eq133140 x
       have r₂ := eq41179 x x x
       grind)
    | exact resolve eq133140 eq41179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41179 eq133140
  have eq133596 : ∀ X0 : G, (M.op X0 X0) = y ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq133385
       have i₂ := eq181 x x
       grind)
    | (have i₁ := eq133385
       have i₂ := eq181 X0 x
       grind)
    | exact superpose eq181 eq133385
    | exact resolve eq133385 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133612 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq181 X0 x
       have i₂ := eq133385
       grind)
    | exact superpose eq133385 eq181
    | exact resolve eq181 eq133385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133709 : y = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66587 x
       have i₂ := eq133385
       grind)
    | exact superpose eq133385 eq66587
    | exact resolve eq66587 eq133385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133385
  have eq133847 : x = (M.op x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq133709
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq133709
    | exact resolve eq133709 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133709
  have eq134235 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x X1) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq180 x X0 X1
       have i₂ := eq133847
       grind)
    | exact superpose eq133847 eq180
    | exact resolve eq180 eq133847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq134237 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq181 X0 x
       have i₂ := eq133847
       grind)
    | exact superpose eq133847 eq181
    | exact resolve eq181 eq133847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq134334 : x = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq66587 x
       have i₂ := eq133847
       grind)
    | exact superpose eq133847 eq66587
    | exact resolve eq66587 eq133847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133847
  have eq134432 : y = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq134334
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq134334
    | exact resolve eq134334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134334
  have eq134492 : ∀ X1 : G, x = (M.op x X1) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq134237 eq134235
    | exact resolve eq134235 eq134237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134235
  have eq134566 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq134432 eq134492
    | exact resolve eq134492 eq134432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134492
  have eq135685 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq67301 sF0 x
       have i₂ := eq134237 sF0
       grind)
    | exact superpose eq134237 eq67301
    | exact resolve eq67301 eq134237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67301
  have eq135703 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x (σ y)) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq256 X0 X1 sF4
       have i₂ := eq134237 sF4
       grind)
    | exact superpose eq134237 eq256
    | exact resolve eq256 eq134237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq135931 : ∀ X1 : G, (M.op x X1) = (M.op x (σ y)) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq134237 eq135703
    | exact resolve eq135703 eq134237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135703
  have eq135942 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq135685 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq135685
    | (have j0 := eq135685 X0
       grind)
    | exact resolve eq135685 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135685
  have eq136315 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X1) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq134432 eq135931
    | exact resolve eq135931 eq134432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135931
  have eq136326 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq135942
    | (have j0 := eq135942 X0
       grind)
    | exact resolve eq135942 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135942
  have eq136625 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X1) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq26 eq136315
    | (have j0 := eq136315 X1
       grind)
    | exact resolve eq136315 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136315
  have eq136633 : x = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq134237 eq136326
    | exact resolve eq136326 eq134237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134237 eq136326
  have eq136824 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq134566 eq136625
    | (have j1 := eq134566 (σ y)
       grind)
    | exact resolve eq136625 eq134566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134566 eq136625
  have eq136830 : (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq134432 eq136633
    | exact resolve eq136633 eq134432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134432 eq136633
  have eq136932 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq136824 eq27
    | exact resolve eq27 eq136824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136824
  have eq137015 : y = (σ y) := by
    first
    | (have r₁ := eq136932
       have r₂ := eq136830
       grind)
    | exact resolve eq136932 eq136830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136830 eq136932
  have eq137049 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq137015
       grind)
    | exact superpose eq137015 eq18
    | exact resolve eq18 eq137015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq137050 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq137015
       grind)
    | exact superpose eq137015 eq24
    | exact resolve eq24 eq137015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137188 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (σ y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq137050 eq454
    | exact resolve eq454 eq137050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq145916 : ∀ X0 X1 : G, (M.op X0 X0) = (σ y) ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq66588 X1 X0
       have i₂ := eq133596 X1
       grind)
    | exact superpose eq133596 eq66588
    | (have j1 := eq133596 X1
       grind)
    | exact resolve eq66588 eq133596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66588 eq133596
  have eq146578 : ∀ X0 X1 : G, (M.op X1 X1) = x ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq145916 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq145916
    | (have j0 := eq145916 X0 X1
       grind)
    | exact resolve eq145916 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq145916
  have eq147815 : ∀ X0 : G, x = (σ x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq66587 x
       have i₂ := eq133612 X0
       grind)
    | exact superpose eq133612 eq66587
    | (have j1 := eq133612 X0
       grind)
    | exact resolve eq66587 eq133612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66587 eq133612
  have eq147965 : ∀ X0 : G, x = (σ x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq147815 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq147815
    | (have j0 := eq147815 X0
       grind)
    | exact resolve eq147815 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147815
  have eq148121 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq147965 X0
       have i₂ := eq137015
       grind)
    | exact superpose eq137015 eq147965
    | exact resolve eq147965 eq137015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137015 eq147965
  have eq148637 : ∀ X1 : G, (k (σ y) X1) = (M.op X1 (σ y)) ∨ x = (σ x) := by
    intro X1
    first
    | (have i₁ := eq1482 x X1
       have i₂ := eq148121 x
       grind)
    | exact superpose eq148121 eq1482
    | exact resolve eq1482 eq148121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157758 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x (σ y))) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq67302 sF4 X1
       have i₂ := eq146578 X0 sF4
       grind)
    | exact superpose eq146578 eq67302
    | (have j1 := eq146578 X1 X1
       grind)
    | exact resolve eq67302 eq146578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67302
  have eq157987 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq137049 eq157758
    | (have j0 := eq157758 X0 X1
       grind)
    | exact resolve eq157758 eq137049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157758
  have eq158441 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq20 eq157987
    | (have j0 := eq157987 X0 X1
       grind)
    | exact resolve eq157987 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157987
  have eq158811 : ∀ X1 : G, x = (σ (M.op x y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X1
    first
    | exact superpose eq146578 eq158441
    | (have j0 := eq158441 x X1
       have j1 := eq146578 X1 X1
       grind)
    | exact resolve eq158441 eq146578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146578 eq158441
  have eq159052 : ∀ X1 : G, (M.op X1 X1) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X1
    first
    | exact superpose eq148121 eq158811
    | (have j0 := eq158811 X1
       have j1 := eq148121 X1
       grind)
    | exact resolve eq158811 eq148121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148121 eq158811
  have eq159414 : ∀ X1 : G, (k (σ y) X1) = (M.op X1 (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X1
    first
    | (have i₁ := eq1482 X1 X1
       have i₂ := eq159052 X1
       grind)
    | exact superpose eq159052 eq1482
    | exact resolve eq1482 eq159052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482 eq159052
  have eq178681 : (M.op x y) = (k (σ y) x) ∨ x = (σ x) := by
    first
    | exact superpose eq148637 eq137049
    | exact resolve eq137049 eq148637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178683 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq148637 eq26
    | (have j1 := eq148637 (σ x)
       grind)
    | exact resolve eq26 eq148637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148637
  have eq179915 : (τ (M.op (σ x) (σ y))) = (k (σ y) (τ (σ x))) ∨ x = (σ x) := by
    first
    | exact superpose eq178683 eq137188
    | exact resolve eq137188 eq178683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137188 eq178683
  have eq179922 : (τ (M.op (σ x) (σ y))) = (k (σ y) x) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq179915
    | exact resolve eq179915 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq179915
  have eq179928 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq178681 eq179922
    | exact resolve eq179922 eq178681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178681 eq179922
  have eq179935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq179928 eq14
    | exact resolve eq14 eq179928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179928
  have eq179984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq179935
    | exact resolve eq179935 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179935
  have eq179985 : x = (σ x) := by
    first
    | (have r₁ := eq179984
       have r₂ := eq27
       grind)
    | exact resolve eq179984 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179984
  have eq179987 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq179985
       grind)
    | exact superpose eq179985 eq22
    | exact resolve eq22 eq179985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq179989 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq179985
       grind)
    | exact superpose eq179985 eq39
    | exact resolve eq39 eq179985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq180018 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq137049
       have i₂ := eq179985
       grind)
    | exact superpose eq179985 eq137049
    | exact resolve eq137049 eq179985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137049 eq179985
  have eq180043 : (σ x) = (τ (σ x)) := by
    first
    | exact superpose eq179987 eq15
    | exact resolve eq15 eq179987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179987
  have eq180383 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq180018 eq26
    | exact resolve eq26 eq180018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq180417 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq180383 eq27
    | exact resolve eq27 eq180383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq180383
  have eq198931 : (M.op x y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq159414 eq180018
    | exact resolve eq180018 eq159414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159414 eq180018
  have eq200331 : (σ (M.op x y)) = (k (σ (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq198931 eq179989
    | exact resolve eq179989 eq198931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179989
  have eq200335 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq137050 eq200331
    | exact resolve eq200331 eq137050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137050 eq200331
  have eq200344 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq200335
    | exact resolve eq200335 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq200335
  have eq200353 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq198931 eq200344
    | exact resolve eq200344 eq198931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198931 eq200344
  have eq200362 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq200353
       have r₂ := eq180417
       grind)
    | exact resolve eq200353 eq180417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200353
  have eq200365 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq200362 eq28
    | exact resolve eq28 eq200362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq200413 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq200362 eq180417
    | exact resolve eq180417 eq200362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180417 eq200362
  have eq200553 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq200365 eq180043
    | exact resolve eq180043 eq200365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180043 eq200365
  have eq200620 : False := by grind
  exact eq200620

/-- `Equation3926`: `x ◇ y = (x ◇ (y ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pyx_x_pyx_Equation3926 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3926 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3926.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X0)) X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq21 X0 (M.op X1 X0) x
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X1
       have r₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq45 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq53 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq25 X0 X0
       grind)
    | exact resolve eq13 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq47
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 X2)) X0) = (σ (M.op (τ X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op X1 X2)
       have i₂ := eq43 X1 X2 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 X2)) X0) = (τ (M.op (σ X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (M.op X1 X2) X0
       have i₂ := eq43 X1 X2 (σ X0)
       grind)
    | exact superpose eq43 eq47
    | exact resolve eq47 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq212 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op X1 (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1 (τ X0)
       have i₂ := eq25 (τ X0) X1
       grind)
    | exact superpose eq25 eq100
    | exact resolve eq100 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq266 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq80
    | exact resolve eq80 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq80 X0 X0
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq80 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq80 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq282 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq287 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq282 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq282 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq302 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1 (σ X0)
       have i₂ := eq25 (σ X0) X1
       grind)
    | exact superpose eq25 eq101
    | exact resolve eq101 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq508 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) ≠ (σ (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (k (σ (M.op X0 X1)) X2) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq287 (M.op X0 X1) X2
       have i₂ := eq43 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq43 eq287
    | (have j0 := eq287 (M.op X0 X1) X2
       grind)
    | exact resolve eq287 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq517 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (k (σ (M.op X0 X1)) X2) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq508 X0 X1 X2
       have i₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq508
    | (have j0 := eq508 X0 X1 X2
       grind)
    | exact resolve eq508 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq518 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) X2) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq517 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq539 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ (M.op X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq518 X1 (τ X0) X0
       grind)
    | exact superpose eq518 eq212
    | exact resolve eq212 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq540 : ∀ X0 X1 X2 : G, (σ (k (M.op X1 X2) X0)) = (M.op (σ X0) (σ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op X1 X2) X0
       have i₂ := eq518 X1 X2 (σ X0)
       grind)
    | exact superpose eq518 eq15
    | exact resolve eq15 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq566 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X2))) = (M.op (σ X0) (σ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq540 X0 X1 X2
       have i₂ := eq43 X1 X2 X0
       grind)
    | exact superpose eq43 eq540
    | exact resolve eq540 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq645 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) X1)) = (M.op (σ (M.op (τ X0) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 (σ (M.op X1 (τ X0))) x
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq21
    | exact resolve eq21 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 : G, (M.op (σ (M.op X1 (τ X0))) X0) = (M.op (σ (M.op X1 (τ X0))) (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ (M.op X1 (τ X0))) X0
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq25
    | exact resolve eq25 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1 (σ (M.op X2 (τ (M.op X0 X1))))
       have i₂ := eq539 (M.op X0 X1) X2
       grind)
    | exact superpose eq539 eq21
    | exact resolve eq21 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 X1 : G, (M.op (σ (M.op X1 (τ X0))) X0) = (σ (M.op (M.op X1 (τ X0)) (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq646 X0 X1
       have i₂ := eq566 (M.op X1 (τ X0)) (τ X0) X1
       grind)
    | exact superpose eq566 eq646
    | exact resolve eq646 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq646
  have eq672 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = (M.op (σ (M.op X1 (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 X1
       have i₂ := eq21 X1 (τ X0) (M.op (τ X0) X1)
       grind)
    | exact superpose eq21 eq659
    | exact resolve eq659 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq702 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op (τ (M.op X0 X1)) X2)
       have i₂ := eq652 X0 X1 X2
       grind)
    | exact superpose eq652 eq10
    | exact resolve eq10 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq826 : ∀ X0 X1 X3 : G, (τ (τ (M.op X0 X1))) = (M.op (τ (τ (M.op X0 X1))) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq702 (τ (M.op X0 X1)) x x
       have i₂ := eq702 X0 X1 x
       grind)
    | exact superpose eq702 eq702
    | exact resolve eq702 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 X1)) X2) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (τ (M.op X0 X1)) X2 X2
       have i₂ := eq702 X0 X1 X2
       grind)
    | exact superpose eq702 eq43
    | exact resolve eq43 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq851 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (σ (M.op (τ (τ (M.op X0 X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq539 (τ (M.op X0 X1)) X2
       have i₂ := eq702 X0 X1 (σ (M.op X2 (τ (τ (M.op X0 X1)))))
       grind)
    | exact superpose eq702 eq539
    | exact resolve eq539 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq877 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq645 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq645
    | exact resolve eq645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq1270 : ∀ X0 X1 X2 : G, (τ (M.op (σ X2) (τ (τ (M.op X0 X1))))) = (k (τ (τ (τ (M.op X0 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302 X2 (τ (τ (M.op X0 X1)))
       have i₂ := eq826 X0 X1 (σ X2)
       grind)
    | exact superpose eq826 eq302
    | exact resolve eq302 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq1417 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq302 X0 X1
       have i₂ := eq840 X1 (σ X0) X0
       grind)
    | exact superpose eq840 eq302
    | exact resolve eq302 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq840
  have eq1792 : ∀ X0 X1 X2 : G, (M.op X2 (τ (τ (M.op X0 X1)))) = (τ (M.op (σ X2) (τ (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1417 X2 (τ (M.op X0 X1))
       have i₂ := eq702 X0 X1 (σ X2)
       grind)
    | exact superpose eq702 eq1417
    | exact resolve eq1417 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3284 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (k (σ X1) X2) (σ (τ X0))) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 (τ X2))
       have i₂ := eq266 X1 X2 (τ X0)
       grind)
    | exact superpose eq266 eq18
    | (have j1 := eq266 X1 X2 (τ X0)
       grind)
    | exact resolve eq18 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq3325 : ∀ X0 X1 X2 : G, (M.op X0 (k (σ X1) X2)) = (k (σ (k X1 (τ X2))) X0) ∨ (σ (τ X0)) = (M.op (k (σ X1) X2) (σ (τ X0))) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3284 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3284
    | (have j0 := eq3284 X0 X1 X2
       grind)
    | exact resolve eq3284 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284
  have eq3350 : ∀ X0 X1 X2 : G, (M.op X0 (k (σ X1) X2)) = (k (k (σ X1) X2) X0) ∨ (σ (τ X0)) = (M.op (k (σ X1) X2) (σ (τ X0))) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3325 X0 X1 X2
       have i₂ := eq18 X2 X1
       grind)
    | exact superpose eq18 eq3325
    | (have j0 := eq3325 X0 X1 X2
       grind)
    | exact resolve eq3325 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3325
  have eq3366 : ∀ X0 X1 X2 : G, (M.op X0 (k (σ X1) X2)) = (k (k (σ X1) X2) X0) ∨ (σ (τ X0)) = (M.op (k (σ X1) X2) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3350 X0 X1 X2
       have j1 := eq12 (k (σ X1) X2) X0
       grind)
    | (have r₁ := eq3350 X0 X1 X2
       have r₂ := eq12 (k (σ X1) X2) X1
       grind)
    | exact resolve eq3350 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq3380 : ∀ X0 X1 X2 : G, (M.op X0 (k (σ X1) X2)) = (k (k (σ X1) X2) X0) ∨ (M.op (k (σ X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3366 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3366
    | (have j0 := eq3366 X0 X1 X2
       grind)
    | exact resolve eq3366 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366
  have eq3900 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq58 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq3923 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3900 (σ x)
       have i₂ := eq80 x x
       grind)
    | exact superpose eq80 eq3900
    | (have j0 := eq3900 (σ X0)
       have j1 := eq80 X0 X0
       grind)
    | exact resolve eq3900 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq3900
  have eq3952 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3923 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3923
  have eq3967 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3952 X0
       have j1 := eq280 X0
       grind)
    | (have r₁ := eq3952 X0
       have r₂ := eq280 X0
       grind)
    | exact resolve eq3952 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq3952
  have eq3973 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3967 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq3967
    | (have j0 := eq3967 X0
       grind)
    | exact resolve eq3967 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3967
  have eq10090 : ∀ X0 X1 : G, (τ (τ (M.op (σ (σ X0)) X1))) = (M.op X0 (τ (τ (M.op X1 (σ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1792 X1 (σ (σ X0)) X0
       have i₂ := eq1417 (σ X0) X1
       grind)
    | exact superpose eq1417 eq1792
    | exact resolve eq1792 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq11770 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (k (τ X0) (τ X0))
       have i₂ := eq3973 (τ X0)
       grind)
    | exact superpose eq3973 eq17
    | (have j1 := eq3973 (τ X0)
       grind)
    | exact resolve eq17 eq3973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq11851 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11770 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq11770
    | (have j0 := eq11770 X0
       grind)
    | exact resolve eq11770 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11770
  have eq11879 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11851 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11851
    | (have j0 := eq11851 X0
       grind)
    | exact resolve eq11851 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11851
  have eq11902 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11879 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11879
    | (have j0 := eq11879 X0
       grind)
    | exact resolve eq11879 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11879
  have eq12302 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (k (τ X0) (τ X0))
       have i₂ := eq11902 (τ X0)
       grind)
    | exact superpose eq11902 eq17
    | (have j1 := eq11902 (τ X0)
       grind)
    | exact resolve eq17 eq11902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11902
  have eq12347 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12302 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq12302
    | (have j0 := eq12302 X0
       grind)
    | exact resolve eq12302 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12302
  have eq12385 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12347 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12347
    | (have j0 := eq12347 X0
       grind)
    | exact resolve eq12347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12347
  have eq13127 : ∀ X0 : G, (σ X0) = (σ (k X0 (k (τ (σ X0)) X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq45 (σ X0) X0 X0
       have i₂ := eq12385 (σ X0)
       grind)
    | exact superpose eq12385 eq45
    | (have j1 := eq12385 (σ X0)
       grind)
    | exact resolve eq45 eq12385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq12385
  have eq13193 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq13127 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13127
    | (have j0 := eq13127 X0
       grind)
    | exact resolve eq13127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13127
  have eq13237 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13193 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13193
    | (have j0 := eq13193 X0
       grind)
    | exact resolve eq13193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13193
  have eq13316 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13237 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq13237
    | (have j0 := eq13237 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq13237 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13237
  have eq13391 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13316 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13316
  have eq15819 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq84 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq15820 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq15819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15819
  have eq15823 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15820 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15820
    | (have j0 := eq15820 X0
       grind)
    | exact resolve eq15820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15820
  have eq17686 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15823 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15823
    | exact resolve eq15823 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15823
  have eq17815 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17686 X0
       have i₂ := eq59 X0 X0
       grind)
    | exact superpose eq59 eq17686
    | (have j0 := eq17686 X0
       grind)
    | exact resolve eq17686 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17686
  have eq17993 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq17815 X0
       grind)
    | exact superpose eq17815 eq11
    | (have j1 := eq17815 X0
       grind)
    | exact resolve eq11 eq17815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17815
  have eq18090 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17993 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq17993
    | (have j0 := eq17993 X0
       grind)
    | exact resolve eq17993 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17993
  have eq18121 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18090 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq18090 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq18090 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18090
  have eq18196 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq18121 (σ X0)
       grind)
    | exact superpose eq18121 eq15
    | exact resolve eq15 eq18121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18203 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0 X0
       have i₂ := eq18121 (τ X0)
       grind)
    | exact superpose eq18121 eq59
    | exact resolve eq59 eq18121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq18256 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18203 X0
       have i₂ := eq18121 X0
       grind)
    | exact superpose eq18121 eq18203
    | exact resolve eq18203 eq18121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18203
  have eq18262 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18196 X0
       have i₂ := eq18121 X0
       grind)
    | exact superpose eq18121 eq18196
    | exact resolve eq18196 eq18121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18121 eq18196
  have eq18661 : ∀ X0 : G, (σ (τ X0)) = (σ (k (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13391 (τ X0)
       have i₂ := eq18256 X0
       grind)
    | exact superpose eq18256 eq13391
    | exact resolve eq13391 eq18256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13391
  have eq18749 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18661 X0
       have i₂ := eq18 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq18 eq18661
    | (have j0 := eq18661 X0
       grind)
    | exact resolve eq18661 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18661
  have eq18798 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18749 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18749
    | (have j0 := eq18749 X0
       grind)
    | exact resolve eq18749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18749
  have eq19531 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ (τ X0)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq18798 (τ X0)
       grind)
    | exact superpose eq18798 eq17
    | (have j1 := eq18798 (τ X0)
       grind)
    | exact resolve eq17 eq18798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18798
  have eq19580 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (τ (τ X0)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19531 X0
       have i₂ := eq18256 X0
       grind)
    | exact superpose eq18256 eq19531
    | (have j0 := eq19531 X0
       grind)
    | exact resolve eq19531 eq18256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19531
  have eq19632 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (τ (τ X0)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19580 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq19580
    | (have j0 := eq19580 X0
       grind)
    | exact resolve eq19580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19580
  have eq19666 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (τ X0)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19632 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19632
    | (have j0 := eq19632 X0
       grind)
    | exact resolve eq19632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19632
  have eq19694 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (τ X0)) = (τ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19666 X0
       have i₂ := eq18256 X0
       grind)
    | exact superpose eq18256 eq19666
    | (have j0 := eq19666 X0
       grind)
    | exact resolve eq19666 eq18256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19666
  have eq24810 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (τ (τ (σ X0))) = (τ (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq19694 (σ X0)
       have i₂ := eq18262 X0
       grind)
    | exact superpose eq18262 eq19694
    | exact resolve eq19694 eq18262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19694
  have eq24936 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (τ (τ (σ X0))) = (τ (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq24810 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq24810
    | (have j0 := eq24810 X0
       grind)
    | exact resolve eq24810 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24810
  have eq24972 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (τ (σ X0))) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24936 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq24936
    | (have j0 := eq24936 X0
       grind)
    | exact resolve eq24936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24936
  have eq25006 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24972 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24972
    | (have j0 := eq24972 X0
       grind)
    | exact resolve eq24972 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24972
  have eq27924 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (τ X0) = (σ (M.op (τ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X0 x
       have i₂ := eq25006 X0
       grind)
    | exact superpose eq25006 eq851
    | (have j1 := eq25006 X0
       grind)
    | exact resolve eq851 eq25006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq25006
  have eq96056 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (τ X0) = (σ (M.op (τ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq27924 X0 X1
       grind)
    | exact superpose eq27924 eq10
    | (have j1 := eq27924 X0 X1
       grind)
    | exact resolve eq10 eq27924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27924
  have eq96236 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ X0) = (σ (M.op (τ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96056 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96056
    | (have j0 := eq96056 X0 X1
       grind)
    | exact resolve eq96056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96056
  have eq97032 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (τ (σ X0)) = (σ (M.op (τ (τ (σ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96236 (σ X0) X1
       have i₂ := eq18262 X0
       grind)
    | exact superpose eq18262 eq96236
    | (have j0 := eq96236 (σ X0) X1
       grind)
    | exact resolve eq96236 eq18262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96236
  have eq97255 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (τ (σ X0)) = (σ (M.op (τ (τ (σ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97032 X0 X1
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq97032
    | (have j0 := eq97032 X0 X1
       grind)
    | exact resolve eq97032 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97032
  have eq97331 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = X0 ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97255 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97255
    | (have j0 := eq97255 X0 X1
       grind)
    | exact resolve eq97255 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97255
  have eq99011 : ∀ X0 X1 : G, (σ (τ (τ (M.op (σ (σ (τ X0))) X1)))) = X0 ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97331 X0 (τ (τ (M.op X1 (σ (σ (τ X0))))))
       have i₂ := eq10090 (τ X0) X1
       grind)
    | exact superpose eq10090 eq97331
    | (have j0 := eq97331 X0 X1
       grind)
    | exact resolve eq97331 eq10090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99256 : ∀ X0 X1 : G, (τ (M.op (σ (σ (τ X0))) X1)) = X0 ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq99011 X0 X1
       have i₂ := eq11 (τ (M.op (σ (σ (τ X0))) X1))
       grind)
    | exact superpose eq11 eq99011
    | (have j0 := eq99011 X0 X1
       grind)
    | exact resolve eq99011 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99011
  have eq99312 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (τ (M.op (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99256 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq99256
    | (have j0 := eq99256 X0 X1
       grind)
    | exact resolve eq99256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99256
  have eq100598 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (k (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99312 (τ X0) X1
       have i₂ := eq18256 X0
       grind)
    | exact superpose eq18256 eq99312
    | (have j0 := eq99312 (τ X0) X1
       grind)
    | exact resolve eq99312 eq18256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99312
  have eq100887 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) (M.op X0 X0)) ∨ (τ X0) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100598 X0 X1
       have i₂ := eq18 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq18 eq100598
    | (have j0 := eq100598 X0 X1
       grind)
    | exact resolve eq100598 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq100598
  have eq100998 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ X0) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100887 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq100887
    | (have j0 := eq100887 X0 X1
       grind)
    | exact resolve eq100887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100887
  have eq101087 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ X0) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100998 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq100998
    | (have j0 := eq100998 X0 X1
       grind)
    | exact resolve eq100998 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100998
  have eq102342 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ (τ X0)) = (τ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq101087 (τ X0) X1
       grind)
    | exact superpose eq101087 eq17
    | (have j1 := eq101087 (τ X0) X1
       grind)
    | exact resolve eq17 eq101087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101087
  have eq102420 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (τ (τ X0)) = (τ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq102342 X0 X1
       have i₂ := eq18256 X0
       grind)
    | exact superpose eq18256 eq102342
    | (have j0 := eq102342 X0 X1
       grind)
    | exact resolve eq102342 eq18256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102342
  have eq102548 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (τ (τ X0)) = (τ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq102420 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq102420
    | (have j0 := eq102420 X0 X1
       grind)
    | exact resolve eq102420 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102420
  have eq102641 : ∀ X0 X1 : G, (τ (τ X0)) = (τ (M.op (τ X0) X1)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq102548 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq102548
    | (have j0 := eq102548 X0 X1
       grind)
    | exact resolve eq102548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102548
  have eq107657 : ∀ X0 X1 : G, (τ (τ X0)) = (τ (τ (τ (M.op (σ (σ (τ X0))) X1)))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq102641 X0 (τ (τ (M.op X1 (σ (σ (τ X0))))))
       have i₂ := eq10090 (τ X0) X1
       grind)
    | exact superpose eq10090 eq102641
    | (have j0 := eq102641 X0 X1
       grind)
    | exact resolve eq102641 eq10090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10090 eq102641
  have eq107868 : ∀ X0 X1 : G, (τ (τ X0)) = (τ (τ (τ (M.op (σ X0) X1)))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107657 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107657
    | (have j0 := eq107657 X0 X1
       grind)
    | exact resolve eq107657 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107657
  have eq164084 : ∀ X0 X1 : G, (τ (τ (M.op (σ X0) X1))) = (σ (τ (τ X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (τ (τ (M.op (σ X0) X1)))
       have i₂ := eq107868 X0 X1
       grind)
    | exact superpose eq107868 eq11
    | (have j1 := eq107868 X0 X1
       grind)
    | exact resolve eq11 eq107868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107868
  have eq164251 : ∀ X0 X1 : G, (τ X0) = (τ (τ (M.op (σ X0) X1))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq164084 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq164084
    | (have j0 := eq164084 X0 X1
       grind)
    | exact resolve eq164084 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164084
  have eq166172 : ∀ X0 X1 : G, (τ X0) = (τ (τ (τ (M.op (σ (σ X0)) X1)))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq164251 X0 (τ (M.op X1 (σ (σ X0))))
       have i₂ := eq1417 (σ X0) X1
       grind)
    | exact superpose eq1417 eq164251
    | (have j0 := eq164251 X0 X1
       grind)
    | exact resolve eq164251 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417 eq164251
  have eq188566 : ∀ X0 X1 : G, (σ (τ X0)) = (τ (τ (M.op (σ (σ X0)) X1))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (τ (τ (M.op (σ (σ X0)) X1)))
       have i₂ := eq166172 X0 X1
       grind)
    | exact superpose eq166172 eq11
    | (have j1 := eq166172 X0 X1
       grind)
    | exact resolve eq11 eq166172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166172
  have eq188732 : ∀ X0 X1 : G, (τ (τ (M.op (σ (σ X0)) X1))) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq188566 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188566
    | (have j0 := eq188566 X0 X1
       grind)
    | exact resolve eq188566 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188566
  have eq190381 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1270 (σ (σ X0)) X1 x
       have i₂ := eq188732 X0 X1
       grind)
    | exact superpose eq188732 eq1270
    | (have j1 := eq188732 X0 X1
       grind)
    | exact resolve eq1270 eq188732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270 eq188732
  have eq193203 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X1))) = (k (τ X2) (M.op X0 X1)) ∨ (k X2 (M.op X2 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq190381 X2 (M.op X0 X1)
       have i₂ := eq877 X0 X1 X2
       grind)
    | exact superpose eq877 eq190381
    | (have j0 := eq190381 X2 X1
       grind)
    | exact resolve eq190381 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq190381
  have eq193667 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X2)) = X2 ∨ (M.op X0 X1) = (k (τ X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193203 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq193203
    | (have j0 := eq193203 X0 X1 X2
       grind)
    | exact resolve eq193203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193203
  have eq200319 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (M.op X1 X2) = (k (τ (σ X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq193667 X1 X2 (σ X0)
       grind)
    | exact superpose eq193667 eq53
    | (have j1 := eq193667 X1 X2 (σ X0)
       grind)
    | exact resolve eq53 eq193667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq193667
  have eq200470 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X0 X0)))) ∨ (M.op X1 X2) = (k (τ (σ X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200319 X0 X1 X2
       have i₂ := eq18262 X0
       grind)
    | exact superpose eq18262 eq200319
    | (have j0 := eq200319 X0 X1 X2
       grind)
    | exact resolve eq200319 eq18262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200319
  have eq200617 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X1 X2) = (k (τ (σ X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200470 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq200470
    | (have j0 := eq200470 X0 X1 X2
       grind)
    | exact resolve eq200470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200470
  have eq200735 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X1 X2) = (k (τ (σ X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200617 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq200617
    | (have j0 := eq200617 X0 X1 X2
       grind)
    | exact resolve eq200617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200617
  have eq200786 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X1 X2) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200735 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq200735
    | (have j0 := eq200735 X0 X1 X2
       grind)
    | exact resolve eq200735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200735
  have eq202145 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq200786 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200786
  have eq202576 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq202145 (σ X0)
       have i₂ := eq18262 X0
       grind)
    | exact superpose eq18262 eq202145
    | exact resolve eq202145 eq18262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18262 eq202145
  have eq202724 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq202576 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq202576
    | (have j0 := eq202576 X0
       grind)
    | exact resolve eq202576 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202576
  have eq250179 : ∀ X0 : G, (σ (τ X0)) ≠ X0 ∨ (σ (k (τ X0) (M.op (τ X0) (τ X0)))) = X0 ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq202724 (τ X0)
       have i₂ := eq97331 X0 (τ X0)
       grind)
    | exact superpose eq97331 eq202724
    | (have j1 := eq97331 X0 x
       grind)
    | exact resolve eq202724 eq97331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97331 eq202724
  have eq250276 : ∀ X0 : G, (σ (k (τ X0) (M.op (τ X0) (τ X0)))) = X0 ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq250179 X0
       grind)
    | (have r₁ := eq250179 X0
       have r₂ := eq11 X0
       grind)
    | exact resolve eq250179 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250179
  have eq250373 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq250276 X0
       have i₂ := eq17 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq17 eq250276
    | (have j0 := eq250276 X0
       grind)
    | exact resolve eq250276 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250276
  have eq250454 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = X0 ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq250373 X0
       have i₂ := eq18256 X0
       grind)
    | exact superpose eq18256 eq250373
    | (have j0 := eq250373 X0
       grind)
    | exact resolve eq250373 eq18256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250373
  have eq250512 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq250454 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq250454
    | (have j0 := eq250454 X0
       grind)
    | exact resolve eq250454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250454
  have eq251950 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (σ (k (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq250512 (τ X0)
       grind)
    | exact superpose eq250512 eq17
    | (have j1 := eq250512 (τ X0)
       grind)
    | exact resolve eq17 eq250512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250512
  have eq252031 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (σ (τ X0)) = (σ (k (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq251950 X0
       have i₂ := eq18256 X0
       grind)
    | exact superpose eq18256 eq251950
    | (have j0 := eq251950 X0
       grind)
    | exact resolve eq251950 eq18256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251950
  have eq252159 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (σ (τ X0)) = (σ (k (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq252031 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq252031
    | (have j0 := eq252031 X0
       grind)
    | exact resolve eq252031 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252031
  have eq252259 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (k (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq252159 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq252159
    | (have j0 := eq252159 X0
       grind)
    | exact resolve eq252159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252159
  have eq252318 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq252259 X0
       have i₂ := eq17 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq17 eq252259
    | (have j0 := eq252259 X0
       grind)
    | exact resolve eq252259 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252259
  have eq252364 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq252318 X0
       have i₂ := eq18256 X0
       grind)
    | exact superpose eq18256 eq252318
    | (have j0 := eq252318 X0
       grind)
    | exact resolve eq252318 eq18256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18256 eq252318
  have eq252405 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq252364 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq252364
    | (have j0 := eq252364 X0
       grind)
    | exact resolve eq252364 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252364
  have eq252426 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq252405 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq252405
    | (have j0 := eq252405 X0
       grind)
    | exact resolve eq252405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252405
  have eq252427 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq252426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252426
  have eq252605 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3380 X0 X1 (M.op (σ X1) (σ X1))
       have i₂ := eq252427 (σ X1)
       grind)
    | exact superpose eq252427 eq3380
    | exact resolve eq3380 eq252427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3380 eq252427
  have eq256913 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X0) X1 x
       have i₂ := eq252605 X0 X1
       grind)
    | exact superpose eq252605 eq21
    | (have j1 := eq252605 X1 X0
       grind)
    | exact resolve eq21 eq252605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq256932 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ X0) X2) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq702 (σ X0) X1 X2
       have i₂ := eq252605 X0 X1
       grind)
    | exact superpose eq252605 eq702
    | (have j1 := eq252605 X1 X0
       grind)
    | exact resolve eq702 eq252605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq252605
  have eq258562 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq256913 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq256913
    | (have j0 := eq256913 X1 X1 X2
       grind)
    | exact resolve eq256913 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256913
  have eq260089 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq258562 (τ X1) X0 X2
       grind)
    | exact superpose eq258562 eq17
    | (have j1 := eq258562 X0 X0 X2
       grind)
    | exact resolve eq17 eq258562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq258562
  have eq264937 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq260089 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq260089
    | (have j0 := eq260089 X1 X1 X2
       grind)
    | exact resolve eq260089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260089
  have eq265642 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq264937 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq264937
    | (have j0 := eq264937 X0 X1 X2
       grind)
    | exact resolve eq264937 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264937
  have eq280676 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (k (σ X2) (σ X0)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq256932 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq256932
    | (have j0 := eq256932 (σ X0) X2 X2
       grind)
    | exact resolve eq256932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256932
  have eq281333 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq280676 X0 X1 X2
       have i₂ := eq15 X2 X0
       grind)
    | exact superpose eq15 eq280676
    | (have j0 := eq280676 X0 X1 X2
       grind)
    | exact resolve eq280676 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280676
  have eq284850 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq281333 x X0 y
       grind)
    | exact superpose eq281333 eq16
    | (have j1 := eq281333 x X0 x
       grind)
    | exact resolve eq16 eq281333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281333
  have eq285457 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq284850 X0
       have j1 := eq265642 X0 x X0
       grind)
    | (have r₁ := eq284850 X0
       have r₂ := eq265642 y x x
       grind)
    | exact resolve eq284850 eq265642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265642 eq284850
  have eq286370 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq672 X0 x
       have i₂ := eq285457 (τ X0)
       grind)
    | exact superpose eq285457 eq672
    | exact resolve eq672 eq285457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq292150 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq286370 (σ y)
       grind)
    | exact superpose eq286370 eq16
    | exact resolve eq16 eq286370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286370
  have eq292689 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq292150
       have i₂ := eq285457 y
       grind)
    | exact superpose eq285457 eq292150
    | exact resolve eq292150 eq285457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285457 eq292150
  have eq292690 : False := by grind
  exact eq292690

/-- `Equation3927`: `x ◇ y = (x ◇ (y ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation3927 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3927 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3927.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq84 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq207 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1041 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq207 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq207
    | (have j0 := eq207 (σ X0) (σ X1)
       grind)
    | exact resolve eq207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq3660 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq84 (σ X1) X1
       grind)
    | (have r₁ := eq13 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq84 (M.op (M.op (σ X1) (σ X1)) X1) X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3676 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq3677 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3676 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3676
  have eq3679 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3660 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3660
  have eq3680 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3679 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3679
  have eq3684 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3677 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3677
    | (have j0 := eq3677 X0
       grind)
    | exact resolve eq3677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3677
  have eq3736 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq3684 X0
       grind)
    | exact superpose eq3684 eq38
    | (have j1 := eq3684 X0
       grind)
    | exact resolve eq38 eq3684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3684
  have eq3760 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3736 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3736
    | (have j0 := eq3736 X0
       grind)
    | exact resolve eq3736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736
  have eq3761 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3760 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3760
  have eq3764 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3761 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3761
    | exact resolve eq3761 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3786 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3761 X0
       grind)
    | exact superpose eq3761 eq11
    | exact resolve eq11 eq3761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3761
  have eq3845 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3764 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq3764
    | exact resolve eq3764 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3764
  have eq3967 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3845 X0
       grind)
    | exact superpose eq3845 eq11
    | exact resolve eq11 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845
  have eq4076 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3967 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3967
    | exact resolve eq3967 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3967
  have eq4692 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4719 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4692 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4692
    | exact resolve eq4692 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4692
  have eq4758 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4719 X0
       have i₂ := eq4076 X0
       grind)
    | exact superpose eq4076 eq4719
    | exact resolve eq4719 eq4076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4781 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq4758
  have eq22812 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1041 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq1041
    | (have j0 := eq1041 (τ X0) (τ X1)
       grind)
    | exact resolve eq1041 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1041
  have eq22888 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22812 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq22812
    | (have j0 := eq22812 X0 X1
       grind)
    | exact resolve eq22812 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22812
  have eq22942 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22888 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22888
    | (have j0 := eq22888 X0 X1
       grind)
    | exact resolve eq22888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22888
  have eq22995 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22942 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq22942
    | (have j0 := eq22942 X0 X1
       grind)
    | exact resolve eq22942 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22942
  have eq23045 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22995 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22995
    | (have j0 := eq22995 X0 X1
       grind)
    | exact resolve eq22995 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22995
  have eq23087 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23045 X0 X1
       have i₂ := eq3786 (σ (τ X1))
       grind)
    | exact superpose eq3786 eq23045
    | (have j0 := eq23045 X0 X1
       grind)
    | exact resolve eq23045 eq3786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23045
  have eq23127 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23087 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq23087
    | (have j0 := eq23087 X0 X1
       grind)
    | exact resolve eq23087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23087
  have eq23164 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23127 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq23127
    | (have j0 := eq23127 X0 X1
       grind)
    | exact resolve eq23127 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq23127
  have eq23199 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23164 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq23164
    | (have j0 := eq23164 X0 X1
       grind)
    | exact resolve eq23164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23164
  have eq23226 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23199 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23199
    | (have j0 := eq23199 X0 X1
       grind)
    | exact resolve eq23199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23199
  have eq23249 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23226 X0 X1
       have i₂ := eq4076 X1
       grind)
    | exact superpose eq4076 eq23226
    | (have j0 := eq23226 X0 X1
       grind)
    | exact resolve eq23226 eq4076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23226
  have eq35055 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X1)
       have i₂ := eq3680 (σ X0) X1
       grind)
    | exact superpose eq3680 eq30
    | (have j1 := eq3680 (σ X0) X1
       grind)
    | exact resolve eq30 eq3680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3680
  have eq35157 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35055 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq35055
    | (have j0 := eq35055 X0 X1
       grind)
    | exact resolve eq35055 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35055
  have eq35257 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35157 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35157
    | (have j0 := eq35157 X0 X1
       grind)
    | exact resolve eq35157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35157
  have eq35352 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35257 X0 X1
       have i₂ := eq3786 X1
       grind)
    | exact superpose eq3786 eq35257
    | (have j0 := eq35257 X0 X1
       grind)
    | exact resolve eq35257 eq3786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3786 eq35257
  have eq35431 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35352 X0 X1
       have i₂ := eq4076 X1
       grind)
    | exact superpose eq4076 eq35352
    | (have j0 := eq35352 X0 X1
       grind)
    | exact resolve eq35352 eq4076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4076 eq35352
  have eq35484 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35431 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35431
    | (have j0 := eq35431 X0 X1
       grind)
    | exact resolve eq35431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35431
  have eq37999 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq35484 X0 X1
       grind)
    | exact superpose eq35484 eq11
    | (have j1 := eq35484 X0 X1
       grind)
    | exact resolve eq11 eq35484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35484
  have eq38494 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37999 x y
       grind)
    | exact superpose eq37999 eq16
    | (have j1 := eq37999 x y
       grind)
    | exact resolve eq16 eq37999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37999
  have eq39520 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38494
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq38494
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq38494 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38494
  have eq39523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq39520
  have eq39524 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq39523
  have eq39527 : x ≠ x ∨ x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq39524
       grind)
    | exact superpose eq39524 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq39524
       grind)
    | exact resolve eq13 eq39524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39528 : x ≠ x ∨ x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq39527
  have eq39529 : x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq39528
  have eq40075 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq23249 x y
       have i₂ := eq39529
       grind)
    | exact superpose eq39529 eq23249
    | (have j0 := eq23249 x y
       grind)
    | exact resolve eq23249 eq39529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23249 eq39529
  have eq40080 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq40075
  have eq40081 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq40080
  have eq40101 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40081
       grind)
    | exact superpose eq40081 eq16
    | exact resolve eq16 eq40081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40081
  have eq40647 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40101
       have i₂ := eq39524
       grind)
    | exact superpose eq39524 eq40101
    | exact resolve eq40101 eq39524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39524 eq40101
  have eq40648 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq40647
  have eq40649 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq40648
  have eq40675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4781 y
       have i₂ := eq40649
       grind)
    | exact superpose eq40649 eq4781
    | exact resolve eq4781 eq40649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40649
  have eq40691 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq40675
       have r₂ := eq16
       grind)
    | exact resolve eq40675 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40675
  have eq41248 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq40691
       grind)
    | exact superpose eq40691 eq10
    | exact resolve eq10 eq40691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40691
  have eq41375 : x = (M.op y y) := by
    first
    | (have i₁ := eq41248
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41248
    | exact resolve eq41248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41248
  have eq41503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4781 y
       have i₂ := eq41375
       grind)
    | exact superpose eq41375 eq4781
    | exact resolve eq4781 eq41375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4781 eq41375
  have eq41519 : False := by grind
  exact eq41519

/-- `Equation3927`: `x ◇ y = (x ◇ (y ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation3927 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3927 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3927.models_iff G M).mp hM
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
  have eq266 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq280 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq269 (σ X0)
       grind)
    | exact superpose eq269 eq15
    | exact resolve eq15 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq280
    | exact resolve eq280 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq280
  have eq342 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq346 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       have j1 := eq343 X0 X1
       grind)
    | (have r₁ := eq342 X0 X1
       have r₂ := eq343 X0 X1
       grind)
    | exact resolve eq342 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq343
  have eq429 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq346 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq346
    | exact resolve eq346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq346 X0 X1
       grind)
    | exact superpose eq346 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq346 X0 (σ X0)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq346 X0 X1
       grind)
    | exact resolve eq13 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq448 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq442 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq456 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq448 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq448 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq448 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq489 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
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
  have eq551 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq489 X0 (τ X1)
       grind)
    | exact superpose eq489 eq17
    | (have j1 := eq489 X0 (τ X1)
       grind)
    | exact resolve eq17 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq557 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq489 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq964 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq551 (τ X0) X1
       grind)
    | exact superpose eq551 eq18
    | (have j1 := eq551 (τ X0) X1
       grind)
    | exact resolve eq18 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq551
  have eq973 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq964 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq964
    | (have j0 := eq964 X0 X1
       grind)
    | exact resolve eq964 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq984 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq973 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq973
    | (have j0 := eq973 X0 X1
       grind)
    | exact resolve eq973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq985 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq984 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq984
    | (have j0 := eq984 X0 X1
       grind)
    | exact resolve eq984 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1040 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq429 X0 X1
       grind)
    | exact superpose eq429 eq985
    | (have j1 := eq429 X0 X1
       grind)
    | exact resolve eq985 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1079 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1040 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1212 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq557 X1 X0
       have i₂ := eq1079 X0 X1
       grind)
    | exact superpose eq1079 eq557
    | (have j0 := eq557 X1 X0
       have j1 := eq1079 X0 X1
       grind)
    | (have r₁ := eq557 X1 X0
       have r₂ := eq1079 X0 X1
       grind)
    | exact resolve eq557 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq1225 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) (τ (σ y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1079 (σ x) (σ y)
       grind)
    | exact superpose eq1079 eq16
    | (have j1 := eq1079 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq1231 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1212 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1238 : (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1225
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1225
    | exact resolve eq1225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1238
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1238
    | exact resolve eq1238 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1260 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have r₁ := eq1257
       have r₂ := eq16
       grind)
    | exact resolve eq1257 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1477 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1231 (σ X0) X1
       grind)
    | exact superpose eq1231 eq22
    | (have j1 := eq1231 (σ X0) X1
       grind)
    | exact resolve eq22 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1231
  have eq1517 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1477 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1477
    | (have j0 := eq1477 X0 X1
       grind)
    | exact resolve eq1477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1534 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1517 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1517
    | (have j0 := eq1517 X0 X1
       grind)
    | exact resolve eq1517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq2661 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1534 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1534
    | exact resolve eq1534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq2764 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2661 y x
       grind)
    | exact superpose eq2661 eq16
    | (have j1 := eq2661 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq2661 y x
       grind)
    | exact resolve eq16 eq2661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2661
  have eq2787 : x = (k y x) := by grind
  clear eq2764
  have eq2860 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq429 x y
       have i₂ := eq2787
       grind)
    | exact superpose eq2787 eq429
    | (have j0 := eq429 x y
       grind)
    | exact resolve eq429 eq2787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq2787
  have eq2863 : x = (M.op x y) := by grind
  clear eq2860
  have eq2867 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1260
       have i₂ := eq2863
       grind)
    | exact superpose eq2863 eq1260
    | exact resolve eq1260 eq2863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq2863
  have eq2875 : False := by grind
  exact eq2875

/-- `Equation3927`: `x ◇ y = (x ◇ (y ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3927 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3927 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3927.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq136 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq138 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq3257 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq138 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq138 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq138 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq13 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq3267 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3257 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3257
  have eq3268 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3267
  have eq3363 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3268 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3268
    | exact resolve eq3268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3268
  have eq3413 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3363 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3363
    | (have j0 := eq3363 X0 X1
       grind)
    | exact resolve eq3363 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363
  have eq3458 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3413 X0 X1
       grind)
    | exact superpose eq3413 eq10
    | (have j1 := eq3413 X0 X1
       grind)
    | exact resolve eq10 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3499 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3458 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3458
    | (have j0 := eq3458 X0 X1
       grind)
    | exact resolve eq3458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458
  have eq3528 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq3499 X0 (σ X1)
       grind)
    | exact superpose eq3499 eq28
    | (have j1 := eq3499 X0 (σ X1)
       grind)
    | exact resolve eq28 eq3499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3499
  have eq3678 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq4200 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq3528 (σ X0) X1
       grind)
    | exact superpose eq3528 eq37
    | (have j1 := eq3528 (σ X0) X1
       grind)
    | exact resolve eq37 eq3528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3528
  have eq4266 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4200 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4200
    | (have j0 := eq4200 X0 X1
       grind)
    | exact resolve eq4200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4200
  have eq4299 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4266 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4266
    | (have j0 := eq4266 X0 X1
       grind)
    | exact resolve eq4266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4266
  have eq4309 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4299 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4299
    | (have j0 := eq4299 X0 X1
       grind)
    | exact resolve eq4299 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4299
  have eq4515 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4309 X0 X1
       grind)
    | exact superpose eq4309 eq11
    | (have j1 := eq4309 X0 X1
       grind)
    | exact resolve eq11 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309
  have eq5392 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4515 x y
       grind)
    | exact superpose eq4515 eq16
    | (have j1 := eq4515 x y
       grind)
    | exact resolve eq16 eq4515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4515
  have eq5424 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5392
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5392
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5392
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5392
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5392 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5392
       have i₂ := eq3413 x y
       grind)
    | exact superpose eq3413 eq5392
    | (have j1 := eq3413 x y
       grind)
    | (have r₁ := eq5392
       have r₂ := eq3413 x y
       grind)
    | (have r₁ := eq5392
       have r₂ := eq3413 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5392
       have r₂ := eq3413 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5392 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3413 eq5392
  have eq5428 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5425
  have eq5429 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq5428
  have eq5430 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5424
  have eq5431 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5430
  have eq5435 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5429
       grind)
    | exact superpose eq5429 eq16
    | exact resolve eq16 eq5429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5429
  have eq5436 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5435
       have r₂ := eq22 x
       grind)
    | exact resolve eq5435 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5435
  have eq5442 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3678 x y
       have i₂ := eq5436
       grind)
    | exact superpose eq5436 eq3678
    | (have j0 := eq3678 x y
       grind)
    | exact resolve eq3678 eq5436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3678 eq5436
  have eq5447 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5442
  have eq5448 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5447
  have eq5460 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5448
       grind)
    | exact superpose eq5448 eq16
    | exact resolve eq16 eq5448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5448
  have eq5476 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5460
       have i₂ := eq5431
       grind)
    | exact superpose eq5431 eq5460
    | exact resolve eq5460 eq5431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5431 eq5460
  have eq5477 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5476
  have eq5478 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5477
  have eq5479 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5478
       grind)
    | exact superpose eq5478 eq16
    | exact resolve eq16 eq5478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5478
  have eq5480 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5479
       have r₂ := eq22 x
       grind)
    | exact resolve eq5479 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5479
  have eq5481 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5480
       grind)
    | exact superpose eq5480 eq16
    | exact resolve eq16 eq5480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5482 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5480
       grind)
    | exact superpose eq5480 eq10
    | exact resolve eq10 eq5480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5480
  have eq5533 : x = y := by
    first
    | (have i₁ := eq5482
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5482
    | exact resolve eq5482 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5482
  have eq5534 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5481
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5481
    | exact resolve eq5481 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5481
  have eq5535 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5534
       have i₂ := eq5533
       grind)
    | exact superpose eq5533 eq5534
    | exact resolve eq5534 eq5533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5533 eq5534
  have eq5536 : False := by grind
  exact eq5536

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation3997 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
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
  have eq291 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq291 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq291 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq291 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq311 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq292 (σ X0)
       grind)
    | exact superpose eq292 eq15
    | exact resolve eq15 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq292 (τ X0)
       grind)
    | exact superpose eq292 eq31
    | exact resolve eq31 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq324 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq317 X0
       have i₂ := eq292 X0
       grind)
    | exact superpose eq292 eq317
    | exact resolve eq317 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq330 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq311 X0
       have i₂ := eq292 X0
       grind)
    | exact superpose eq292 eq311
    | exact resolve eq311 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq311
  have eq685 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq702 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1
       have i₂ := eq330 X0
       grind)
    | exact superpose eq330 eq685
    | (have j0 := eq685 X0 X1
       grind)
    | exact resolve eq685 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq863 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq702 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq702
    | exact resolve eq702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq897 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq863 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq863
    | (have j0 := eq863 X0 X1
       grind)
    | exact resolve eq863 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq863
  have eq902 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq897 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq897 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq897 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq897 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq903 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq902 X0 X1
       have i₂ := eq324 X0
       grind)
    | exact superpose eq324 eq902
    | (have j0 := eq902 X0 X1
       grind)
    | exact resolve eq902 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq902
  have eq904 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq903 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq903
    | (have j0 := eq903 X0 X1
       grind)
    | exact resolve eq903 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq905 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq904 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq904
    | exact resolve eq904 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq904 (σ X0) X1
       grind)
    | exact superpose eq904 eq15
    | (have j1 := eq904 (σ X0) X1
       grind)
    | exact resolve eq15 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq935 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq911 X0 X1
       have i₂ := eq330 X0
       grind)
    | exact superpose eq330 eq911
    | (have j0 := eq911 X0 X1
       grind)
    | exact resolve eq911 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq964 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq905 (τ X1) X0
       grind)
    | exact superpose eq905 eq17
    | (have j1 := eq905 (τ X1) X0
       grind)
    | exact resolve eq17 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq905
  have eq1095 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq964 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq964
    | exact resolve eq964 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1155 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1095 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1095
    | (have j0 := eq1095 X0 X1
       grind)
    | exact resolve eq1095 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq2861 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq935 x y
       grind)
    | exact superpose eq935 eq16
    | (have j1 := eq935 x y
       grind)
    | exact resolve eq16 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2882 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq935 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq2911 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2861
       have i₂ := eq1155 y x
       grind)
    | exact superpose eq1155 eq2861
    | (have j1 := eq1155 y x
       grind)
    | (have r₁ := eq2861
       have r₂ := eq1155 y x
       grind)
    | exact resolve eq2861 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2861
  have eq2912 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2911
  have eq2916 : y ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2912
       grind)
    | exact superpose eq2912 eq12
    | exact resolve eq12 eq2912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2917 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2912
       grind)
    | exact superpose eq2912 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2912
       grind)
    | exact resolve eq13 eq2912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2912
  have eq2922 : y = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2917
  have eq2923 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2916
       have r₂ := eq2922
       grind)
    | exact resolve eq2916 eq2922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916 eq2922
  have eq2948 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2882 x y
       have i₂ := eq2923
       grind)
    | exact superpose eq2923 eq2882
    | (have j0 := eq2882 x y
       grind)
    | exact resolve eq2882 eq2923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882 eq2923
  have eq2980 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2948
  have eq2981 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2980
  have eq3065 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2981
       grind)
    | exact superpose eq2981 eq16
    | exact resolve eq16 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3068 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2981
       grind)
    | exact superpose eq2981 eq12
    | exact resolve eq12 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3069 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2981
       grind)
    | exact superpose eq2981 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981
  have eq3074 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq3069
       have r₂ := eq330 x
       grind)
    | exact resolve eq3069 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3069
  have eq3075 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3068
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3068
    | exact resolve eq3068 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068
  have eq3076 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3074
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3074
    | exact resolve eq3074 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074
  have eq3077 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3076
       have i₂ := eq330 x
       grind)
    | exact superpose eq330 eq3076
    | exact resolve eq3076 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq3076
  have eq3078 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq3077
       have r₂ := eq3075
       grind)
    | exact resolve eq3077 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075 eq3077
  have eq3086 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1155 y x
       have i₂ := eq3078
       grind)
    | exact superpose eq3078 eq1155
    | (have j0 := eq1155 y x
       grind)
    | exact resolve eq1155 eq3078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq3078
  have eq3135 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq3086
       have r₂ := eq3065
       grind)
    | exact resolve eq3086 eq3065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq3308 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3065
       have i₂ := eq3135
       grind)
    | exact superpose eq3135 eq3065
    | exact resolve eq3065 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065 eq3135
  have eq3318 : False := by grind
  exact eq3318

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_x_pxx_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq100 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) x X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq140 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq100 X0 X2
       grind)
    | (have i₁ := eq100 X0 X2
       have i₂ := eq100 X0 (M.op X0 X0)
       grind)
    | exact superpose eq100 eq100
    | exact resolve eq100 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq150 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    grind
  clear eq100
  have eq312 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq316 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq720 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq316 x y
       grind)
    | exact superpose eq316 eq16
    | (have j1 := eq316 x y
       grind)
    | exact resolve eq16 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq4861 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq105
  have eq4913 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4861 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4861
  have eq14216 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq312 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq312
    | exact resolve eq312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq14308 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14216 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq14216
    | (have j0 := eq14216 X0 X1
       grind)
    | exact resolve eq14216 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14216
  have eq40956 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq148 X0 X1
       grind)
    | exact superpose eq148 eq150
    | (have j1 := eq148 X0 X1
       grind)
    | exact resolve eq150 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq41008 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq41014 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq40956 X0 X1
       have j1 := eq41008 X0 X1
       grind)
    | (have r₁ := eq40956 X0 X1
       have r₂ := eq41008 X0 X1
       grind)
    | exact resolve eq40956 eq41008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40956 eq41008
  have eq41081 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41014 X1 X1
       have i₂ := eq4913 X1 X1
       grind)
    | exact superpose eq4913 eq41014
    | (have j1 := eq4913 X0 X1
       grind)
    | exact resolve eq41014 eq4913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4913
  have eq41189 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq41014 X0 x
       grind)
    | exact superpose eq41014 eq9
    | exact resolve eq9 eq41014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41014
  have eq41838 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41081 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41081
  have eq42151 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41838 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41838
  have eq42471 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq42151 (σ X0)
       grind)
    | exact superpose eq42151 eq15
    | exact resolve eq15 eq42151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42524 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq42471 X0
       have i₂ := eq42151 X0
       grind)
    | exact superpose eq42151 eq42471
    | exact resolve eq42471 eq42151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42471
  have eq43091 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140 (σ X0) X1 X2
       have i₂ := eq42524 X0
       grind)
    | exact superpose eq42524 eq140
    | exact resolve eq140 eq42524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43101 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (k (σ (M.op X0 X0)) (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41189 (σ X0) x
       have i₂ := eq42524 X0
       grind)
    | exact superpose eq42524 eq41189
    | exact resolve eq41189 eq42524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41189
  have eq43134 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (k (M.op X0 X0) (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43101 X0 X1
       have i₂ := eq15 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq15 eq43101
    | exact resolve eq43101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43101
  have eq43210 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43134 X0 X1
       have i₂ := eq42151 (M.op X0 X0)
       grind)
    | exact superpose eq42151 eq43134
    | exact resolve eq43134 eq42151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42151 eq43134
  have eq45036 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X0) X1)) = (M.op (σ (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43210 (M.op X0 X0) X1
       have i₂ := eq140 X0 (M.op X0 X0) X2
       grind)
    | (have i₁ := eq43210 (M.op X0 X0) X1
       have i₂ := eq140 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq140 eq43210
    | exact resolve eq43210 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq43210
  have eq45297 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45036 X0 X1 X2
       have i₂ := eq9 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq9 eq45036
    | exact resolve eq45036 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45036
  have eq53829 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq720
       have i₂ := eq14308 x y
       grind)
    | exact superpose eq14308 eq720
    | (have j1 := eq14308 (σ x) (σ y)
       grind)
    | (have r₁ := eq720
       have r₂ := eq14308 x y
       grind)
    | (have r₁ := eq720
       have r₂ := eq14308 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq720
       have r₂ := eq14308 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq720 eq14308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq14308
  have eq53830 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq53829
  have eq53832 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53830
       have i₂ := eq42524 y
       grind)
    | exact superpose eq42524 eq53830
    | exact resolve eq53830 eq42524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53830
  have eq1041228 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53832
       grind)
    | exact superpose eq53832 eq16
    | exact resolve eq16 eq53832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53832
  have eq1041229 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1041228
       have r₂ := eq42524 x
       grind)
    | exact resolve eq1041228 eq42524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041228
  have eq1041232 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1041229
       grind)
    | exact superpose eq1041229 eq10
    | exact resolve eq10 eq1041229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041229
  have eq1041386 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1041232
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1041232
    | exact resolve eq1041232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041232
  have eq1041448 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1041386
       grind)
    | exact superpose eq1041386 eq16
    | exact resolve eq16 eq1041386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041386
  have eq1041449 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1041448
       have r₂ := eq42524 x
       grind)
    | exact resolve eq1041448 eq42524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42524 eq1041448
  have eq1041680 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1041449
       grind)
    | exact superpose eq1041449 eq10
    | exact resolve eq10 eq1041449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041449
  have eq1041834 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1041680
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1041680
    | exact resolve eq1041680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041680
  have eq1041835 : x = (M.op y y) := by grind
  clear eq1041834
  have eq1041894 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43091 y X1 x
       have i₂ := eq1041835
       grind)
    | exact superpose eq1041835 eq43091
    | exact resolve eq43091 eq1041835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43091
  have eq1041922 : ∀ X0 X1 : G, (M.op (σ x) X1) = (σ (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45297 y X1 x
       have i₂ := eq1041835
       grind)
    | exact superpose eq1041835 eq45297
    | exact resolve eq45297 eq1041835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45297 eq1041835
  have eq1052874 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1041894 (σ y) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq1041894 X0 (σ y)
       grind)
    | exact superpose eq1041894 eq16
    | exact resolve eq16 eq1041894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041894
  have eq1053917 : False := by grind
  exact eq1053917

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pyy_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq32 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) x X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | (have j1 := eq56 (σ X0)
       grind)
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq85 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq104 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 x (M.op X0 X0)
       have i₂ := eq32 X0 x
       grind)
    | (have i₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq32 X0 x
       grind)
    | exact superpose eq32 eq13
    | (have r₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq32 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 x (M.op X0 X0)
       have r₂ := eq32 X0 x
       grind)
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq105 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq294 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X0) (σ X0)
       have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq85 X1 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq297 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq294 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq298 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq300 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq298
    | (have j0 := eq298 X0 X1
       grind)
    | exact resolve eq298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq306 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq300 X0 X1
       have j1 := eq296 X0 X1
       grind)
    | (have r₁ := eq300 X0 X1
       have r₂ := eq296 X0 X1
       grind)
    | (have r₁ := eq300 X0 X0
       have r₂ := eq296 X0 X0
       grind)
    | exact resolve eq300 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq300
  have eq491 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq503 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq491 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq491
    | (have j0 := eq491 (τ X0)
       grind)
    | exact resolve eq491 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq503 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq503
    | (have j0 := eq503 X0
       grind)
    | exact resolve eq503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq507 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq504 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq504
    | (have j0 := eq504 X0
       grind)
    | exact resolve eq504 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq514 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq507 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq507
    | (have j0 := eq507 (τ X0)
       grind)
    | exact resolve eq507 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq619 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq306 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq306
    | exact resolve eq306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq306 x y
       grind)
    | exact superpose eq306 eq16
    | (have j1 := eq306 x x
       grind)
    | exact resolve eq16 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq647 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq619
  have eq648 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq647
    | (have j0 := eq647 X1 X1
       grind)
    | exact resolve eq647 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq712 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq648 (τ X1) X0
       grind)
    | exact superpose eq648 eq17
    | (have j1 := eq648 X0 X0
       grind)
    | exact resolve eq17 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq877 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 (σ X0)) = (σ (M.op X0 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq712 X0 X2
       grind)
    | exact superpose eq712 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq712 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq712 X0 X1
       grind)
    | exact resolve eq12 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq894 : ∀ X0 X1 X2 : G, (k X2 (σ X0)) = (σ (M.op X0 (τ X2))) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq877 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq899 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq894 X1 X2 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq894
    | (have j0 := eq894 X1 X2 X2
       grind)
    | exact resolve eq894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 X1 X2 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq894 X1 X2 X0
       grind)
    | exact superpose eq894 eq10
    | (have j1 := eq894 X1 X2 X2
       grind)
    | exact resolve eq10 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq945 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq917 X0 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq917
    | (have j0 := eq917 X0 X1 X2
       grind)
    | exact resolve eq917 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq917
  have eq951 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq899 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq899
    | (have j0 := eq899 X0 X1 X2
       grind)
    | exact resolve eq899 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq994 : ∀ X0 X1 X2 : G, (k X2 (τ X0)) = X2 ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq945 X1 (τ X0) X2
       grind)
    | exact superpose eq945 eq34
    | (have j1 := eq945 X0 (τ X0) X2
       grind)
    | exact resolve eq34 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq1496 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq491 (τ X0)
       have i₂ := eq994 X0 X1 (τ X0)
       grind)
    | exact superpose eq994 eq491
    | (have j0 := eq491 (τ X0)
       have j1 := eq994 X0 X1 x
       grind)
    | exact resolve eq491 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1513 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (τ (k X2 X1)) = (M.op (τ X1) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq994 X1 X2 (τ X0)
       grind)
    | exact superpose eq994 eq17
    | (have j1 := eq994 X1 X2 X2
       grind)
    | exact resolve eq17 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq994
  have eq1517 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1496 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1523 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 X1) ∨ (τ (k X2 X1)) = (M.op (τ X1) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1513 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1513
    | (have j0 := eq1513 X0 X1 X2
       grind)
    | exact resolve eq1513 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq1530 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1517 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1517
    | (have j0 := eq1517 X0 X1
       grind)
    | exact resolve eq1517 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1534 : ∀ X0 X1 X2 : G, (τ (k X2 X1)) = (M.op (τ X1) (τ X2)) ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1523 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1523
    | (have j0 := eq1523 X0 X1 X2
       grind)
    | exact resolve eq1523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1594 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1530 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1530
    | (have j0 := eq1530 X1 X1
       grind)
    | exact resolve eq1530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1643 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1594 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq1594
    | (have j0 := eq1594 X0 X1
       grind)
    | exact resolve eq1594 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1594
  have eq1664 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq491 (τ X0)
       have i₂ := eq1643 (τ X0) X0
       grind)
    | exact superpose eq1643 eq491
    | (have j0 := eq491 (τ X0)
       have j1 := eq1643 X0 (σ (τ X0))
       grind)
    | exact resolve eq491 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1677 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1664 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1664
    | (have j0 := eq1664 X0
       grind)
    | exact resolve eq1664 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664
  have eq1679 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1677 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1677
    | (have j0 := eq1677 X0
       grind)
    | exact resolve eq1677 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq1680 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679
  have eq1762 : ∀ X0 X1 : G, (σ (τ (k X0 X0))) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1680 X0
       have i₂ := eq1534 X1 X0 X0
       grind)
    | exact superpose eq1534 eq1680
    | (have j0 := eq1680 X0
       have j1 := eq1534 X1 X0 x
       grind)
    | exact resolve eq1680 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534 eq1680
  have eq1795 : ∀ X0 X1 : G, (σ (τ (k X0 X0))) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1762 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1762 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1762 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq1803 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1795 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1795
    | (have j0 := eq1795 X0 X1
       grind)
    | exact resolve eq1795 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1837 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1803 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1803
    | (have j0 := eq1803 (σ X0) X1
       grind)
    | exact resolve eq1803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1839 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1803 (τ X0) X1
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq1803
    | (have j0 := eq1803 (τ X0) X1
       grind)
    | exact resolve eq1803 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1803
  have eq2353 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq631
       have i₂ := eq951 y x X0
       grind)
    | exact superpose eq951 eq631
    | (have j1 := eq951 X0 x X0
       grind)
    | (have r₁ := eq631
       have r₂ := eq951 y x x
       grind)
    | exact resolve eq631 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq951
  have eq2354 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq2353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2383 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq491 x
       have i₂ := eq2354 x
       grind)
    | exact superpose eq2354 eq491
    | (have j0 := eq491 x
       grind)
    | exact resolve eq491 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq2388 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1837 x X0
       have i₂ := eq2354 x
       grind)
    | exact superpose eq2354 eq1837
    | (have j0 := eq1837 x X0
       grind)
    | exact resolve eq1837 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837 eq2354
  have eq2411 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq2388 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388
  have eq2415 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2383
  have eq2416 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2415
  have eq2427 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq2411 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq2411 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq2411 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq2477 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq514 (σ x)
       have i₂ := eq2427 (σ x)
       grind)
    | exact superpose eq2427 eq514
    | (have j0 := eq514 (σ x)
       grind)
    | exact resolve eq514 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq2481 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1839 (σ x) X0
       have i₂ := eq2427 (σ x)
       grind)
    | exact superpose eq2427 eq1839
    | (have j0 := eq1839 (σ x) X0
       grind)
    | exact resolve eq1839 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839
  have eq2489 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2427 (σ X0)
       grind)
    | exact superpose eq2427 eq15
    | exact resolve eq15 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427
  have eq2502 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq2481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481
  have eq2505 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by grind
  clear eq2477
  have eq2518 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq2502 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2502
    | exact resolve eq2502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502
  have eq2519 : x = (M.op x x) := by
    first
    | (have i₁ := eq2505
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2505
    | exact resolve eq2505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505
  have eq2623 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq105 x x
       have i₂ := eq2519
       grind)
    | exact superpose eq2519 eq105
    | exact resolve eq105 eq2519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq2633 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2623 X0
       have i₂ := eq2518 x
       grind)
    | exact superpose eq2518 eq2623
    | (have j0 := eq2623 X0
       grind)
    | exact resolve eq2623 eq2518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518 eq2623
  have eq2634 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633
  have eq4124 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq105 (σ x) x
       have i₂ := eq2416
       grind)
    | exact superpose eq2416 eq105
    | exact resolve eq105 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq2416
  have eq4134 : ∀ X0 : G, (σ (k x x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq4124 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq4124
    | (have j0 := eq4124 X0
       grind)
    | exact resolve eq4124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq4136 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq4134 X0
       have i₂ := eq2489 x
       grind)
    | exact superpose eq2489 eq4134
    | (have j0 := eq4134 X0
       grind)
    | exact resolve eq4134 eq2489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2489 eq4134
  have eq4137 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq4136 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq4143 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4137 (σ y)
       grind)
    | exact superpose eq4137 eq16
    | exact resolve eq16 eq4137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq4175 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4143
       have i₂ := eq2634 y
       grind)
    | exact superpose eq2634 eq4143
    | exact resolve eq4143 eq2634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634 eq4143
  have eq4176 : False := by grind
  exact eq4176
