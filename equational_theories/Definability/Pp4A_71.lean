import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq174 (M.op X0 X1)
       grind)
    | exact superpose eq174 eq178
    | exact resolve eq178 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (k X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X0 X1 X2 X3
       have i₂ := eq174 X3
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq182 : ∀ X0 : G, (M.op y (M.op (M.op x y) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq175
    | exact resolve eq175 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (k X0 X0)) (M.op X0 (k X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 X0 X1 X2 X3
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq180
    | exact resolve eq180 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq174 (M.op X0 X0)
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq179 X0 X0
       grind)
    | exact superpose eq179 eq186
    | exact resolve eq186 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq188 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq184
    | exact resolve eq184 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq189 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq187
    | exact resolve eq187 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq191 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (k X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (k X0 X0)) (M.op X0 (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq191
    | exact resolve eq191 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq322 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq406 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq322 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq322
    | exact resolve eq322 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq544 : ∀ X0 : G, (τ X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq181 (τ X0)
       have i₂ := eq406 X0 X0
       grind)
    | exact superpose eq406 eq181
    | exact resolve eq181 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 : G, (M.op X0 (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq188 X0 X0
       have i₂ := eq174 (k X0 X0)
       grind)
    | exact superpose eq174 eq188
    | exact resolve eq188 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (k (τ (k X0 X0)) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq570 (τ X0)
       have i₂ := eq406 X0 X0
       grind)
    | exact superpose eq406 eq570
    | exact resolve eq570 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq188 X0 (k (k X0 X0) (k X0 X0))
       have i₂ := eq570 (k X0 X0)
       grind)
    | exact superpose eq570 eq188
    | exact resolve eq188 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq628 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq181 (k sF4 sF4)
       have i₂ := eq570 sF4
       grind)
    | exact superpose eq570 eq181
    | exact resolve eq181 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq631 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq622 X0
       have i₂ := eq406 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq406 eq622
    | exact resolve eq622 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq622
  have eq634 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq631 X0
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq631
    | exact resolve eq631 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq726 : y = (M.op y (τ (M.op (σ y) (k (σ y) (σ y))))) := by
    first
    | exact superpose eq31 eq634
    | exact resolve eq634 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq778 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = y := by
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
  have eq790 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq1137 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = (k (k X0 X1) (k X0 X1)) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq179
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq179 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (M.op x y) (k X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq182 eq179
    | exact resolve eq179 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1163 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq181 (M.op X1 X0)
       have i₂ := eq179 X1 X0
       grind)
    | exact superpose eq179 eq181
    | exact resolve eq181 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1194 : ∀ X0 : G, (M.op (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1149 eq185
    | exact resolve eq185 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1202 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1194 X0
       have i₂ := eq174 (k (k X0 X0) (k X0 X0))
       grind)
    | exact superpose eq174 eq1194
    | exact resolve eq1194 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1204 : ∀ X0 : G, (M.op (k X0 X0) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1202 X0
       have i₂ := eq626 (k X0 X0)
       grind)
    | exact superpose eq626 eq1202
    | exact resolve eq1202 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1206 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1204 X0
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq1204
    | exact resolve eq1204 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq1204
  have eq1336 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq778
       grind)
    | exact superpose eq778 eq39
    | exact resolve eq39 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq1337 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1336
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1336
    | exact resolve eq1336 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1339 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq1337
    | exact resolve eq1337 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1365 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq192 eq179
    | exact resolve eq179 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq1474 : ∀ X0 : G, (k X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1163 X0 (M.op x (k X0 X0))
       have i₂ := eq1365 X0 x
       grind)
    | exact superpose eq1365 eq1163
    | exact resolve eq1163 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1505 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq1163 (k X0 X0) X0
       have i₂ := eq1206 X0
       grind)
    | exact superpose eq1206 eq1163
    | exact resolve eq1163 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1589 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq189 X0
       have i₂ := eq1505 X0
       grind)
    | exact superpose eq1505 eq189
    | exact resolve eq189 eq1505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1610 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (k (σ y) (σ y))))) := by
    first
    | exact superpose eq1505 eq1163
    | exact resolve eq1163 eq1505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1620 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1474 eq1610
    | exact resolve eq1610 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474 eq1610
  have eq1660 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq181 eq1589
    | exact resolve eq1589 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq3285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1339 eq790
    | exact resolve eq790 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq3293 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq3285
       have r₂ := eq27
       grind)
    | exact resolve eq3285 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq3298 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3293 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3299 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3293 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3293
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3293
       grind)
    | exact resolve eq12 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3301 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3293 eq179
    | exact resolve eq179 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3303 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (k X0 X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3293 eq185
    | exact resolve eq185 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3307 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq3299
  have eq3308 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq3307
  have eq3309 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq3298
  have eq3314 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq3301
    | exact resolve eq3301 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3301
  have eq3316 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3308
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq3308
    | exact resolve eq3308 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308
  have eq3317 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq3309
    | exact resolve eq3309 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq3321 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1339 eq3316
    | exact resolve eq3316 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq3316
  have eq3324 : y = (M.op y (τ (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3314 eq726
    | exact resolve eq726 eq3314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq3388 : y = (M.op y (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq628 eq3324
    | exact resolve eq3324 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324
  have eq3406 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq3321 eq185
    | exact resolve eq185 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq3417 : (τ (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (τ (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3321 eq544
    | exact resolve eq544 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq3444 : (τ (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq3417
    | exact resolve eq3417 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3417
  have eq3453 : (τ (σ x)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1505 eq3444
    | exact resolve eq3444 eq1505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505 eq3444
  have eq3458 : x = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq29 eq3453
    | exact resolve eq3453 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3453
  have eq3935 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3458 eq182
    | exact resolve eq182 eq3458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq3458
  have eq4007 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq3935
       grind)
    | exact superpose eq3935 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq3935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4016 : y ≠ (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq3935
  have eq4018 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq4007
  have eq4024 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4018
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4018
    | exact resolve eq4018 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4018
  have eq4383 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3317 eq90
    | exact resolve eq90 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3317
  have eq4391 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq31 eq4383
    | exact resolve eq4383 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4383
  have eq4657 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4391
       have i₂ := eq4024
       grind)
    | exact superpose eq4024 eq4391
    | exact resolve eq4391 eq4024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4024 eq4391
  have eq4662 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq4657
  have eq4666 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4662
       have r₂ := eq4016
       grind)
    | exact resolve eq4662 eq4016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016 eq4662
  have eq4672 : y = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq4666
       grind)
    | exact superpose eq4666 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq4666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666
  have eq4683 : y = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4672
  have eq4692 : x = (M.op x y) ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4683
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4683
    | exact resolve eq4683 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4683
  have eq4693 : y = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4692
  have eq4802 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq4693
       grind)
    | exact superpose eq4693 eq35
    | exact resolve eq35 eq4693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4693
  have eq4810 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4802
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4802
    | exact resolve eq4802 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4802
  have eq5822 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3314 eq3303
    | exact resolve eq3303 eq3314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3303 eq3314
  have eq5839 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq5822
  have eq5853 : (σ y) = (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq628 eq5839
    | exact resolve eq5839 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq5839
  have eq5883 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X1) (k (σ x) (σ x))) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq5853 eq183
    | exact resolve eq183 eq5853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq5853
  have eq5901 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X1) (σ (M.op x y))) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq3321 eq5883
    | exact resolve eq5883 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321 eq5883
  have eq6461 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3406 eq1589
    | exact resolve eq1589 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq6520 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3293 eq6461
    | exact resolve eq6461 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3293 eq6461
  have eq6577 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5901 eq6520
    | exact resolve eq6520 eq5901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5901 eq6520
  have eq6648 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq6577 eq3406
    | exact resolve eq3406 eq6577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406 eq6577
  have eq6664 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq6648
  have eq6670 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq6664
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq6664
    | exact resolve eq6664 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6664
  have eq6715 : y = (M.op y (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq6670 eq3388
    | exact resolve eq3388 eq6670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388 eq6670
  have eq6763 : y = (M.op y (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq6715
  have eq6792 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq29 eq6763
    | exact resolve eq6763 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6763
  have eq6793 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6792
  have eq6823 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq179 y x
       have i₂ := eq6793
       grind)
    | exact superpose eq6793 eq179
    | exact resolve eq179 eq6793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq6793
  have eq6837 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6823
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6823
    | exact resolve eq6823 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6823
  have eq6851 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq6837
       grind)
    | exact superpose eq6837 eq40
    | exact resolve eq40 eq6837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq6837
  have eq6917 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6851
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6851
    | exact resolve eq6851 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6851
  have eq6932 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq6917
    | exact resolve eq6917 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6917
  have eq7038 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6932 eq1660
    | exact resolve eq1660 eq6932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq23615 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4810 eq1137
    | (have j0 := eq1137 (σ x) (σ y)
       grind)
    | exact resolve eq1137 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq4810
  have eq23711 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23615
  have eq23751 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23711
    | exact resolve eq23711 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23711
  have eq23772 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23751
    | exact resolve eq23751 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23751
  have eq23773 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq23772
  have eq23777 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6932 eq23773
    | exact resolve eq23773 eq6932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23773
  have eq23779 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq23777
       have r₂ := eq27
       grind)
    | exact resolve eq23777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23777
  have eq23796 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq23779 eq1620
    | exact resolve eq1620 eq23779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620 eq23779
  have eq23998 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq23796
    | exact resolve eq23796 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23796
  have eq24010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6932 eq23998
    | exact resolve eq23998 eq6932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6932 eq23998
  have eq24015 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq24010
       have r₂ := eq27
       grind)
    | exact resolve eq24010 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24010
  have eq24018 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24015 eq31
    | exact resolve eq31 eq24015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24015
  have eq24084 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq24018
    | exact resolve eq24018 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24018
  have eq24085 : x = (M.op x y) ∨ x = y := by grind
  clear eq24084
  have eq24090 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq24085
       grind)
    | exact superpose eq24085 eq22
    | exact resolve eq22 eq24085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24085
  have eq24161 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq24090
    | exact resolve eq24090 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24090
  have eq24251 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq24161 eq7038
    | exact resolve eq7038 eq24161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7038
  have eq24416 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24251
  have eq24473 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq24416
    | exact resolve eq24416 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24416
  have eq24587 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24473 eq27
    | exact resolve eq27 eq24473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24473
  have eq24847 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq24587
       have r₂ := eq24161
       grind)
    | exact resolve eq24587 eq24161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24161 eq24587
  have eq24877 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq24847 eq31
    | exact resolve eq31 eq24847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq24847
  have eq24964 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq24877
    | exact resolve eq24877 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq24877
  have eq24965 : x = y := by grind
  clear eq24964
  have eq25003 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24965
       grind)
    | exact superpose eq24965 eq18
    | exact resolve eq18 eq24965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25004 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq24965
       grind)
    | exact superpose eq24965 eq24
    | exact resolve eq24 eq24965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq24965
  have eq25022 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25004
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25004
    | exact resolve eq25004 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25004
  have eq25023 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq25003
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq25003
    | exact resolve eq25003 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25003
  have eq25024 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25022 eq26
    | exact resolve eq26 eq25022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq25022
  have eq25094 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq25024
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq25024
    | exact resolve eq25024 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq25024
  have eq25110 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq25023
       grind)
    | exact superpose eq25023 eq39
    | exact resolve eq39 eq25023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq25023
  have eq25217 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq25110
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25110
    | exact resolve eq25110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25110
  have eq25237 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25094 eq25217
    | exact resolve eq25217 eq25094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25094 eq25217
  have eq25248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq25237
    | exact resolve eq25237 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq25237
  have eq25257 : False := by grind
  exact eq25257

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : y ≠ (M.op x y) ∨ x = y ∨ (M.op x x) = (k y x) := by
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
  have eq81 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq211 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq53 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq54 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq219 eq54
    | exact resolve eq54 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X1 X0)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X0)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq219 eq492
    | exact resolve eq492 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq55 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq56 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq55 X0 x x X3
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq55 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq55 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq55 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq760 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq759 X0 X1 X2 X3
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq759
    | exact resolve eq759 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq761 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq758 X0 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq758
    | exact resolve eq758 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq762 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq757 X0 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq757
    | exact resolve eq757 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq1082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1082
    | exact resolve eq1082 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1086 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1083
       have r₂ := eq28
       grind)
    | exact resolve eq1083 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1088 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1086
    | exact resolve eq1086 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1092 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1088 eq81
    | (have r₁ := eq81
       have r₂ := eq1088
       grind)
    | exact resolve eq81 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1099 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1092
  have eq1100 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1099
  have eq1187 : (τ (M.op (σ x) (σ x))) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1100 eq99
    | exact resolve eq99 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1100
  have eq1194 : (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq68 eq1187
    | exact resolve eq1187 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1197 : (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1194
       have r₂ := eq80
       grind)
    | exact resolve eq1194 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1194
  have eq1200 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq1197
       grind)
    | exact superpose eq1197 eq87
    | exact resolve eq87 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1201 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1197
       grind)
    | exact superpose eq1197 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1202 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1201
  have eq1204 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1202
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1202
    | exact resolve eq1202 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1205 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1200
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq1200
    | exact resolve eq1200 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1200
  have eq1207 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1204
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1204
    | exact resolve eq1204 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1309 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1205 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1310 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1309
  have eq1314 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1310
    | exact resolve eq1310 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1317 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1314
    | exact resolve eq1314 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1431 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq1207
       grind)
    | exact superpose eq1207 eq53
    | exact resolve eq53 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1453 : x = (M.op y (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq211 eq1431
    | exact resolve eq1431 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq1431
  have eq1544 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1317 eq14
    | exact resolve eq14 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1546 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1317 eq54
    | exact resolve eq54 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq1567 : (σ x) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq219 eq1546
    | exact resolve eq1546 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq1654 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq494 (M.op x sF4) (M.op x sF4)
       have i₂ := eq14 (M.op x sF4) sF4 x
       grind)
    | exact superpose eq14 eq494
    | exact resolve eq494 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq1664 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1654 X0
       have i₂ := eq56 X0 sF4
       grind)
    | exact superpose eq56 eq1654
    | exact resolve eq1654 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654
  have eq1855 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 (M.op X0 X0))
       have i₂ := eq717 X0 X0 X0
       grind)
    | exact superpose eq717 eq54
    | exact resolve eq54 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1871 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq753 (M.op x (M.op x x)) x
       have i₂ := eq717 x x x
       grind)
    | exact superpose eq717 eq753
    | exact resolve eq753 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq5132 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1544 (M.op sF4 sF4) x
       have i₂ := eq753 sF4 x
       grind)
    | exact superpose eq753 eq1544
    | exact resolve eq1544 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq1544
  have eq5220 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5132
       have i₂ := eq56 sF4 sF4
       grind)
    | exact superpose eq56 eq5132
    | exact resolve eq5132 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5132
  have eq5232 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq219 eq5220
    | exact resolve eq5220 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq5220
  have eq5420 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5232 eq223
    | exact resolve eq223 eq5232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq5232
  have eq5674 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq761 X0 X1
       grind)
    | exact superpose eq761 eq762
    | exact resolve eq762 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq5833 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5674 (M.op x sF4) (M.op X0 X0)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq5674
    | exact resolve eq5674 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5674
  have eq7416 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq760 X0 X1 X2 X3
       have i₂ := eq761 X0 X1
       grind)
    | exact superpose eq761 eq760
    | exact resolve eq760 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq761
  have eq7584 : ∀ X0 X3 X4 : G, (M.op y (M.op (M.op x y) X0)) = (M.op X3 (M.op (M.op X4 X3) X0)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq7416 x (M.op (M.op x x) (M.op X0 X0)) x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq7416
    | exact resolve eq7416 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7718 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7416 X1 X0 X0 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq7416
    | exact resolve eq7416 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq7740 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7416 (M.op X1 (M.op X2 X3)) (M.op X0 X0) X3 X2
       have i₂ := eq14 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq14 eq7416
    | exact resolve eq7416 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7416
  have eq20265 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1088 eq1855
    | exact resolve eq1855 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq29274 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ y) X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1871 X0 X1
       have i₂ := eq20265 X0
       grind)
    | (have i₁ := eq1871 (σ y) X1
       have i₂ := eq20265 (σ y)
       grind)
    | exact superpose eq20265 eq1871
    | exact resolve eq1871 eq20265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20265
  have eq35382 : y = (M.op (M.op x y) (M.op (σ y) (M.op (σ y) y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq29274 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29274
    | (have j0 := eq29274 y x
       grind)
    | exact resolve eq29274 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29274
  have eq78591 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op x (M.op (M.op x y) X0)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq7584 X0 x x
       have i₂ := eq1207
       grind)
    | exact superpose eq1207 eq7584
    | exact resolve eq7584 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207 eq7584
  have eq128774 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq35382 eq78591
    | exact resolve eq78591 eq35382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35382 eq78591
  have eq129137 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq128774
  have eq129172 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq129137
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq129137
    | exact resolve eq129137 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129137
  have eq129223 : y = (M.op y (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq492 y
       have i₂ := eq129172
       grind)
    | exact superpose eq129172 eq492
    | exact resolve eq492 eq129172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq129172
  have eq131726 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq129223 eq1453
    | exact resolve eq1453 eq129223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453 eq129223
  have eq131817 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq131726
  have eq131856 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq131817 eq30
    | exact resolve eq30 eq131817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq131817
  have eq131947 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq131856
    | exact resolve eq131856 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131856
  have eq131948 : y = (M.op x y) ∨ x = y := by grind
  clear eq131947
  have eq131959 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq131948 eq21
    | exact resolve eq21 eq131948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131961 : ∀ X0 : G, (M.op y (M.op y (M.op X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq131948 eq53
    | exact resolve eq53 eq131948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq132202 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq131959
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq131959
    | exact resolve eq131959 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131959
  have eq132250 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) ∨ x = y := by
    first
    | exact superpose eq132202 eq506
    | exact resolve eq506 eq132202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq132275 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq132202 eq1567
    | exact resolve eq1567 eq132202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq132283 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq132202 eq1855
    | exact resolve eq1855 eq132202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq132313 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq132202 eq5420
    | exact resolve eq5420 eq132202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5420
  have eq132685 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq132313
  have eq132716 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq132275
  have eq132771 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq132685
       have r₂ := eq28
       grind)
    | exact resolve eq132685 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132685
  have eq132786 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq132716
       have r₂ := eq28
       grind)
    | exact resolve eq132716 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132716
  have eq132795 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) ∨ x = y := by
    first
    | exact superpose eq1664 eq132250
    | exact resolve eq132250 eq1664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664 eq132250
  have eq141270 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq132202 eq132795
    | exact resolve eq132795 eq132202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132795
  have eq141352 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) ∨ x = y := by grind
  clear eq141270
  have eq162153 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq132786 eq141352
    | exact resolve eq141352 eq132786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132786 eq141352
  have eq162222 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq162153
  have eq183058 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq132283 eq7718
    | exact resolve eq7718 eq132283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7718 eq132283
  have eq183186 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq183058 X0
       have i₂ := eq1871 X0 sF4
       grind)
    | exact superpose eq1871 eq183058
    | exact resolve eq183058 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871 eq183058
  have eq183291 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq495 eq183186
    | exact resolve eq183186 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq183186
  have eq188304 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq162222 eq183291
    | exact resolve eq183291 eq162222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183291
  have eq188807 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq188304
  have eq190684 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq188807 eq162222
    | exact resolve eq162222 eq188807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162222 eq188807
  have eq190786 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq190684
  have eq191005 : (σ x) = (M.op y (M.op y (M.op (σ x) (σ y)))) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq190786 eq131961
    | exact resolve eq131961 eq190786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190786
  have eq191092 : (σ x) = (M.op y (M.op y (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq191005
  have eq235860 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq132771 eq7740
    | exact resolve eq7740 eq132771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7740 eq132771
  have eq237321 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5833 eq235860
    | exact resolve eq235860 eq5833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5833 eq235860
  have eq260249 : (σ y) = (M.op y (M.op y (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq237321 eq131961
    | exact resolve eq131961 eq237321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131961 eq237321
  have eq260712 : (σ y) = (M.op y (M.op y (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq260249
  have eq261184 : (σ y) = (M.op y (M.op y (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq260712
    | exact resolve eq260712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260712
  have eq271279 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq261184 eq191092
    | exact resolve eq191092 eq261184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191092 eq261184
  have eq271409 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq271279
  have eq271546 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq271409 eq132202
    | exact resolve eq132202 eq271409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132202 eq271409
  have eq271923 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq271546
  have eq272021 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq271923 eq29
    | exact resolve eq29 eq271923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq271923
  have eq272905 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq272021
    | exact resolve eq272021 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq272021
  have eq276015 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq272905 eq131948
    | exact resolve eq131948 eq272905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131948 eq272905
  have eq276224 : x = y := by grind
  clear eq276015
  have eq276768 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq276224
       grind)
    | exact superpose eq276224 eq19
    | exact resolve eq19 eq276224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq276769 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq276224
       grind)
    | exact superpose eq276224 eq25
    | exact resolve eq25 eq276224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq276224
  have eq276982 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq276769
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq276769
    | exact resolve eq276769 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq276769
  have eq277028 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq276982 eq27
    | exact resolve eq27 eq276982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq276982
  have eq278058 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq277028 eq68
    | exact resolve eq68 eq277028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq277028
  have eq278486 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq278058
       have i₂ := eq276768
       grind)
    | exact superpose eq276768 eq278058
    | exact resolve eq278058 eq276768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276768 eq278058
  have eq278651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq278486 eq15
    | exact resolve eq15 eq278486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278486
  have eq278741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq278651
    | exact resolve eq278651 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq278651
  have eq278767 : False := by grind
  exact eq278767

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
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
  clear eq74
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
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
    | (have r₁ := eq112 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq113 (σ X0)
       grind)
    | exact superpose eq113 eq10
    | exact resolve eq10 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq43
    | exact resolve eq43 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq118 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq49
    | exact resolve eq49 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq119 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq118
    | exact resolve eq118 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq116
    | exact resolve eq116 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq122 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq115
    | exact resolve eq115 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq128 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq102
    | exact resolve eq102 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq128
    | exact resolve eq128 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq142 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq113 sF1
       grind)
    | exact superpose eq113 eq139
    | exact resolve eq139 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq145 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq113 sF0
       grind)
    | exact superpose eq113 eq142
    | exact resolve eq142 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq254 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y X0)) (M.op X0 (M.op (M.op (M.op x y) (M.op y X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq113 (τ X0)
       grind)
    | exact superpose eq113 eq34
    | exact resolve eq34 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq379 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq368
    | exact resolve eq368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq381 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq379 X0
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq379
    | exact resolve eq379 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq379
  have eq495 : (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq145 eq122
    | exact resolve eq122 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq518 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq14
    | exact resolve eq14 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq530 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X4 (M.op (M.op X2 X1) (M.op X1 X0))) X3)) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op (M.op X2 X1) (M.op X1 X0)) X4 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op x y) (M.op y X0)) X1)) = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op X2 (M.op (M.op x y) (M.op y X0))) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq55
    | exact resolve eq55 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X5 X1) (M.op (M.op X4 X1) X2))) = (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op (M.op X4 X1) X2) X1 X5 X3
       have i₂ := eq55 X2 X1 X4 X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X0) (M.op (M.op X5 (M.op X4 X0)) (M.op X0 X2))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X0 X2) (M.op X4 X0) X5 X3
       have i₂ := eq55 X2 X0 X1 X4
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) y) = (M.op x (M.op (M.op X2 x) (M.op (M.op X1 x) (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq562 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 x
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op X1 (M.op X0 x)) y)) := by
    intro X0 X1
    first
    | exact superpose eq560 eq14
    | exact resolve eq14 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op (M.op X1 (M.op X0 (σ x))) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq561 eq14
    | exact resolve eq14 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq16
    | exact resolve eq16 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq777 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0)) = (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X3 X1 X2 (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0))
       have i₂ := eq52 X3 X1 X2 X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op (M.op X1 X2) (M.op X2 X3))) X4) = (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 X3))) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X3 X1 X2 (M.op (M.op X5 (M.op (M.op X1 X2) (M.op X2 X3))) X4)
       have i₂ := eq55 X4 (M.op (M.op X1 X2) (M.op X2 X3)) X5 X0
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op (M.op X5 (M.op (M.op X2 X3) (M.op X3 X4))) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) (M.op (M.op X2 X3) (M.op X3 X4)) X5 X1
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq254 eq50
    | exact resolve eq50 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1051 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op (M.op x y) X0)) = (M.op y (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq932 (M.op (M.op x sF0) (M.op sF0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq932
    | exact resolve eq932 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op X2 y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq932 eq55
    | exact resolve eq55 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq1062 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1060 X0 X1 x
       have i₂ := eq14 (M.op sF0 X0) y x
       grind)
    | exact superpose eq14 eq1060
    | exact resolve eq1060 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1104 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq260 eq51
    | exact resolve eq51 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq260
  have eq1125 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1104 eq55
    | exact resolve eq55 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1127 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1125 X0 X1 x
       have i₂ := eq14 (M.op sF4 X0) sF3 x
       grind)
    | exact superpose eq14 eq1125
    | exact resolve eq1125 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1147 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op X1 (σ y))) (M.op (M.op X1 (σ y)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq1127 eq14
    | exact resolve eq14 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1156 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op X1 (σ y))) (M.op (M.op (σ x) (σ y)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq1127 eq1147
    | exact resolve eq1147 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1191 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq558 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq55 X2 X1 X4 X0
       grind)
    | exact superpose eq55 eq558
    | exact resolve eq558 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1194 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op X1 x)) (M.op (M.op X1 x) y)) := by
    intro X0 X1
    first
    | exact superpose eq560 eq558
    | exact resolve eq558 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1248 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1191 x X1 X2 X4 X3
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq1191
    | exact resolve eq1191 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1430 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (τ X0)) X1) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1248 (τ X0) X1 (τ X0) X2
       have i₂ := eq737 X0
       grind)
    | exact superpose eq737 eq1248
    | exact resolve eq1248 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq1248
  have eq4653 : ∀ X0 X1 : G, (M.op (M.op y (M.op (M.op x y) X0)) (M.op X0 (M.op (M.op y (M.op (M.op x y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq254 eq259
    | exact resolve eq259 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq14288 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op y (M.op (M.op x y) X0)) X1)) = (M.op (M.op y (M.op (M.op x y) X0)) (M.op (M.op X2 (M.op y (M.op (M.op x y) X0))) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq254 eq536
    | exact resolve eq536 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq19290 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) X1) = (M.op (M.op y (M.op (M.op x y) X0)) (M.op (M.op X2 (M.op y (M.op (M.op x y) X0))) (M.op X0 (M.op (M.op y (M.op (M.op x y) X0)) X1)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq14288 eq14
    | exact resolve eq14 eq14288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19336 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) X1) = (M.op X0 (M.op (M.op y (M.op (M.op x y) X0)) (M.op X0 (M.op (M.op y (M.op (M.op x y) X0)) X1)))) := by
    intro X0 X1 X3
    first
    | exact superpose eq14288 eq19290
    | exact resolve eq19290 eq14288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14288 eq19290
  have eq19366 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) X1) := by
    intro X0 X1 X3
    first
    | exact superpose eq4653 eq19336
    | exact resolve eq19336 eq4653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653 eq19336
  have eq22208 : ∀ X0 X1 X2 X3 X4 X6 X7 X8 : G, (M.op (M.op X7 (M.op X0 X1)) (M.op (M.op X8 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 (M.op (M.op X6 X1) X3))))) = (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X3))))) := by
    intro X0 X1 X2 X3 X4 X6 X7 X8
    first
    | (have i₁ := eq541 X8 (M.op X0 X1) (M.op X1 (M.op (M.op X6 X1) X3)) X7 x X4
       have i₂ := eq542 X1 X6 X3 x X0 X2
       grind)
    | exact superpose eq542 eq541
    | exact resolve eq541 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq22296 : ∀ X0 X1 X2 X3 X6 X7 X8 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X3)) = (M.op (M.op X7 (M.op X0 X1)) (M.op (M.op X8 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 (M.op (M.op X6 X1) X3))))) := by
    intro X0 X1 X2 X3 X6 X7 X8
    first
    | (have i₁ := eq22208 X0 X1 X2 X3 x X6 X7 X8
       have i₂ := eq14 (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X3)) (M.op X0 X1) x
       grind)
    | exact superpose eq14 eq22208
    | exact resolve eq22208 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22208
  have eq52624 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op (M.op X1 X2) (M.op X2 X3))) X4) = (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 X3))) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq780 X0 X1 X2 X3 X4 X5
       have i₂ := eq777 (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 X3))) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X4)) X1 X2 X3
       grind)
    | exact superpose eq777 eq780
    | exact resolve eq780 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq780
  have eq52625 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op (M.op X1 X2) (M.op X2 X3))) X4) = (M.op X3 (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X4)))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52624 x X1 X2 X3 X4 X5
       have i₂ := eq530 X3 X2 X1 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X4) x
       grind)
    | exact superpose eq530 eq52624
    | exact resolve eq52624 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52624
  have eq53053 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X5 (M.op (M.op X6 X0) (M.op X0 X1))) (M.op (M.op X0 X1) X4)) = (M.op X1 (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X3 (M.op X0 X1)) X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq52625 X6 X0 X1 (M.op (M.op X0 X1) X4) X5
       have i₂ := eq541 (M.op X6 X0) (M.op X0 X1) X4 (M.op X6 X0) X3 X2
       grind)
    | exact superpose eq541 eq52625
    | exact resolve eq52625 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq52625
  have eq53956 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X3 (M.op X0 X1)) X4)) = (M.op (M.op X5 (M.op (M.op X6 X0) (M.op X0 X1))) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq53053 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq562 X1 X0 (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X3 (M.op X0 X1)) X4))
       grind)
    | exact superpose eq562 eq53053
    | exact resolve eq53053 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq53053
  have eq54384 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq787 X0 X1 X2 X3 X4 x
       have i₂ := eq530 X4 X3 X2 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) x
       grind)
    | exact superpose eq530 eq787
    | exact resolve eq787 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq787
  have eq54385 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54384 X0 X1 X2 X3 X4
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq54384
    | exact resolve eq54384 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq54384
  have eq55055 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 (M.op X2 (M.op (M.op X3 X4) (M.op X4 X0)))) (M.op (M.op X2 (M.op (M.op X3 X4) (M.op X4 X0))) X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X5 (M.op X2 (M.op (M.op X3 X4) (M.op X4 X0))) X1
       have i₂ := eq54385 (M.op (M.op X1 (M.op X2 (M.op (M.op X3 X4) (M.op X4 X0)))) (M.op (M.op X2 (M.op (M.op X3 X4) (M.op X4 X0))) X5)) X2 X3 X4 X0
       grind)
    | exact superpose eq54385 eq14
    | exact resolve eq14 eq54385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55188 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 (M.op X2 (M.op (M.op X3 X4) (M.op X4 X0)))) (M.op X0 X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55055 X0 X1 X2 X3 X4 X5
       have i₂ := eq54385 X5 X2 X3 X4 X0
       grind)
    | exact superpose eq54385 eq55055
    | exact resolve eq55055 eq54385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55055
  have eq76686 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq14
    | exact resolve eq14 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq76850 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76686 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq76686
    | exact resolve eq76686 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76686
  have eq76966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq76850 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq76850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq76966
    | exact resolve eq76966 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76966
  have eq76993 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq76980
       have r₂ := eq27
       grind)
    | exact resolve eq76980 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76980
  have eq76997 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq76993
    | exact resolve eq76993 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76993
  have eq76999 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq76997 eq129
    | exact resolve eq129 eq76997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77125 : ∀ X0 X1 X2 : G, (M.op (σ y) X0) = (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (σ y) (σ x)))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq76997 eq54385
    | exact resolve eq54385 eq76997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77127 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq77125 X0 x x
       have i₂ := eq54385 X0 x x sF3 sF2
       grind)
    | exact superpose eq54385 eq77125
    | exact resolve eq77125 eq54385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77125
  have eq78978 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq77127 eq129
    | exact resolve eq129 eq77127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78988 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq77127 eq76997
    | exact resolve eq76997 eq77127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76997
  have eq79251 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq78988
  have eq79325 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq79251
    | exact resolve eq79251 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79251
  have eq79335 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq78978
    | exact resolve eq78978 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78978
  have eq79434 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq79325 eq77127
    | exact resolve eq77127 eq79325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79325
  have eq79545 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq79434
  have eq79959 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq79545 eq119
    | exact resolve eq119 eq79545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79545
  have eq81165 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x (τ (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq558 x X0 x
       have i₂ := eq79959
       grind)
    | exact superpose eq79959 eq558
    | exact resolve eq558 eq79959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79959
  have eq86722 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq77127 eq76999
    | exact resolve eq76999 eq77127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76999 eq77127
  have eq86782 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq86722
  have eq86796 : (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq119 eq86782
    | exact resolve eq86782 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86782
  have eq86826 : (M.op y (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq254 y
       have i₂ := eq86796
       grind)
    | exact superpose eq86796 eq254
    | exact resolve eq254 eq86796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq86832 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1062 X0 y
       have i₂ := eq86796
       grind)
    | exact superpose eq86796 eq1062
    | exact resolve eq1062 eq86796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq86796
  have eq104684 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op x X0))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq86832 (M.op x X0)
       grind)
    | exact superpose eq86832 eq14
    | exact resolve eq14 eq86832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86832
  have eq112649 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1051 eq495
    | exact resolve eq495 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq1051
  have eq761561 : x = (M.op x (M.op y (M.op (M.op x y) y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq86826 eq104684
    | exact resolve eq104684 eq86826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86826 eq104684
  have eq761813 : x = (M.op x (M.op y (M.op (M.op x y) y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq761561
  have eq762447 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq761813 eq19366
    | exact resolve eq19366 eq761813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19366 eq761813
  have eq763268 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79335
       have i₂ := eq762447 y
       grind)
    | exact superpose eq762447 eq79335
    | exact resolve eq79335 eq762447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79335 eq762447
  have eq764025 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq763268
  have eq764242 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq764025
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq764025
    | exact resolve eq764025 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764025
  have eq764508 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq764242 eq81165
    | exact resolve eq81165 eq764242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81165 eq764242
  have eq764756 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq764508 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764508
  have eq764778 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq560 eq764756
    | exact resolve eq764756 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764756
  have eq764779 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq764778
  have eq765000 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq764779 eq66
    | (have r₁ := eq66
       have r₂ := eq764779
       grind)
    | exact resolve eq66 eq764779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq765006 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq764779 eq561
    | exact resolve eq561 eq764779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq765570 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq765000
  have eq765808 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq765570 eq76850
    | exact resolve eq76850 eq765570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76850 eq765570
  have eq765920 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq765808
  have eq766567 : (τ (σ (M.op x y))) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq765920 eq129
    | exact resolve eq129 eq765920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq766644 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) X0) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq765920 eq1127
    | exact resolve eq1127 eq765920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq766645 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ (M.op x y))) (M.op (M.op (σ x) (σ y)) X1))) = X1 ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq765920 eq1156
    | exact resolve eq1156 eq765920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156 eq765920
  have eq767071 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq766567
    | exact resolve eq766567 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq766567
  have eq838935 : ∀ X0 X1 : G, (M.op (M.op X0 (τ (M.op (σ x) (σ x)))) X1) = (M.op (τ (σ y)) X1) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq765006 eq1430
    | exact resolve eq1430 eq765006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430 eq765006
  have eq839383 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (τ (M.op (σ x) (σ x)))) X1) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq838935
    | exact resolve eq838935 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq838935
  have eq839575 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op x x)) X1) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq119 eq839383
    | exact resolve eq839383 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839383
  have eq1879338 : (M.op x (M.op x y)) = (M.op y (M.op (M.op x x) y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq839575 x (M.op (M.op x x) y)
       have i₂ := eq1194 x x
       grind)
    | exact superpose eq1194 eq839575
    | exact resolve eq839575 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1879706 : (M.op x (M.op x y)) = (M.op (M.op x x) (M.op y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq584 x x
       have i₂ := eq839575 x y
       grind)
    | exact superpose eq839575 eq584
    | exact resolve eq584 eq839575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq1938129 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (σ (M.op x y))) (M.op (σ (M.op x y)) X0))) = X0 ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq766644 eq766645
    | exact resolve eq766645 eq766644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766644 eq766645
  have eq1938862 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (σ (M.op x y))) (M.op (σ (M.op x y)) X0))) = X0 ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq1938129 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938129
  have eq2063252 : (M.op x (M.op x y)) = (M.op (M.op x x) (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1879706
       have i₂ := eq767071
       grind)
    | exact superpose eq767071 eq1879706
    | exact resolve eq1879706 eq767071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767071 eq1879706
  have eq2063673 : (M.op x (M.op x y)) = (M.op (M.op x x) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2063252
  have eq2064768 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op x (M.op (M.op X1 x) (M.op x (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2063673 eq545
    | exact resolve eq545 eq2063673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq2065263 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2064768 X0 x
       have i₂ := eq14 sF0 x x
       grind)
    | exact superpose eq14 eq2064768
    | exact resolve eq2064768 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064768
  have eq2067162 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1879338
       have i₂ := eq2065263 x
       grind)
    | exact superpose eq2065263 eq1879338
    | exact resolve eq1879338 eq2065263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879338 eq2065263
  have eq2067467 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2067162
  have eq2381122 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op y (M.op y (M.op x y))))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq112649 eq1938862
    | exact resolve eq1938862 eq112649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112649 eq1938862
  have eq2382670 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op y (M.op y (M.op x y))))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq764779 eq2381122
    | exact resolve eq2381122 eq764779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764779 eq2381122
  have eq2383125 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op y (M.op y (M.op x y))))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2382670
  have eq2383915 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op y (M.op x (M.op x y))))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2067467 eq2383125
    | exact resolve eq2383125 eq2067467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067467 eq2383125
  have eq2384297 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op y (M.op x (M.op x y))))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2383915
  have eq2413033 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X3 (M.op X0 X1)) X4)) = (M.op X1 (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53956 X0 X1 X2 X3 X4 x x
       have i₂ := eq54385 (M.op (M.op X0 X1) X4) x x X0 X1
       grind)
    | exact superpose eq54385 eq53956
    | exact resolve eq53956 eq54385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53956 eq54385
  have eq3845039 : ∀ X0 X1 X2 X3 X6 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X3)) = (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 (M.op (M.op X6 X1) X3))))) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq22296 X0 X1 X2 X3 X6 x x
       have i₂ := eq2413033 X0 X1 x x (M.op (M.op X0 X1) (M.op X1 (M.op (M.op X6 X1) X3)))
       grind)
    | exact superpose eq2413033 eq22296
    | exact resolve eq22296 eq2413033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22296 eq2413033
  have eq3854762 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 x)) (M.op x (M.op x y))) = (M.op x (M.op (M.op X1 x) (M.op (M.op X1 x) (M.op x (M.op x (M.op x y)))))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2063673 eq3845039
    | exact resolve eq3845039 eq2063673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063673 eq3845039
  have eq3860846 : ∀ X0 X1 : G, (M.op x (M.op (M.op X1 x) (M.op x y))) = (M.op (M.op X0 (M.op X1 x)) (M.op x (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq3854762 X0 X1
       have i₂ := eq558 sF0 X1 x
       grind)
    | exact superpose eq558 eq3854762
    | exact resolve eq3854762 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq3854762
  have eq3868875 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 x)) (M.op x (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq53 eq3860846
    | exact resolve eq3860846 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq3860846
  have eq4360561 : y = (M.op y (M.op x (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq3868875 eq839575
    | exact resolve eq839575 eq3868875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839575 eq3868875
  have eq4361201 : y = (M.op y (M.op x (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq4360561
  have eq4362784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq4361201 eq2384297
    | exact resolve eq2384297 eq4361201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384297 eq4361201
  have eq4363217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq4362784
  have eq4363539 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4363217
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4363217
    | exact resolve eq4363217 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363217
  have eq4363767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4363539
    | exact resolve eq4363539 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363539
  have eq4363921 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq4363767
       have r₂ := eq27
       grind)
    | exact resolve eq4363767 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363767
  have eq4364139 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq4363921 eq20
    | exact resolve eq20 eq4363921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4364204 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4363921 eq560
    | exact resolve eq560 eq4363921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq4363921
  have eq4364663 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq4364139
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4364139
    | exact resolve eq4364139 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364139
  have eq4418050 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ (M.op x x)) (M.op (M.op X0 (σ (M.op x x))) (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq518 (M.op x x) X0
       have i₂ := eq4364204 x
       grind)
    | exact superpose eq4364204 eq518
    | exact resolve eq518 eq4364204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq4364204
  have eq4418913 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ (M.op x x)) (M.op (M.op X0 (σ (M.op x x))) (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4418050 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4418050
    | (have j0 := eq4418050 X0
       grind)
    | exact resolve eq4418050 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4418050
  have eq4419289 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op X0 (M.op (σ x) (σ x))) (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4418913 X0
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq4418913
    | exact resolve eq4418913 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq4418913
  have eq4419462 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq596 eq4419289
    | exact resolve eq4419289 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq4419289
  have eq4420169 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X3 (σ x))))) (M.op (σ x) (σ x)))) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4419462 eq55188
    | exact resolve eq55188 eq4419462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419462
  have eq4420549 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4420169 x x x x
       have i₂ := eq55188 sF2 x x x x sF2
       grind)
    | exact superpose eq55188 eq4420169
    | exact resolve eq4420169 eq55188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55188 eq4420169
  have eq4421003 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq4420549 eq27
    | exact resolve eq27 eq4420549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4420549
  have eq4423020 : x = y := by
    first
    | (have r₁ := eq4421003
       have r₂ := eq4364663
       grind)
    | exact resolve eq4421003 eq4364663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364663 eq4421003
  have eq4423030 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4423020
       grind)
    | exact superpose eq4423020 eq18
    | exact resolve eq18 eq4423020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4423031 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4423020
       grind)
    | exact superpose eq4423020 eq24
    | exact resolve eq24 eq4423020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4423020
  have eq4423508 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4423031
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4423031
    | exact resolve eq4423031 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4423031
  have eq4423545 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4423508 eq26
    | exact resolve eq26 eq4423508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4423508
  have eq4425652 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4423545 eq119
    | exact resolve eq119 eq4423545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq4423545
  have eq4426757 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4425652
       have i₂ := eq4423030
       grind)
    | exact superpose eq4423030 eq4425652
    | exact resolve eq4425652 eq4423030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4423030 eq4425652
  have eq4426971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4426757 eq15
    | exact resolve eq15 eq4426757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4426757
  have eq4427498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4426971
    | exact resolve eq4426971 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4426971
  have eq4427644 : False := by grind
  exact eq4427644

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : x ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq109 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq111 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq112 (σ X0)
       grind)
    | exact superpose eq112 eq10
    | exact resolve eq10 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq43
    | exact resolve eq43 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq116 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq75
    | exact resolve eq75 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq119 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq116
    | exact resolve eq116 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq115
    | exact resolve eq115 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq114
    | exact resolve eq114 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq128 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq101
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq101
    | exact resolve eq101 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq128
    | exact resolve eq128 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq128
  have eq254 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : (σ (M.op (k y x) (k y x))) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq121 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq121
    | exact resolve eq121 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq14
    | exact resolve eq14 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X4 (M.op (M.op X2 X1) (M.op X1 X0))) X3)) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op (M.op X2 X1) (M.op X1 X0)) X4 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X3 X2) (M.op X2 X0)))) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X3 X2) (M.op X2 X0)) X2 X4 X1
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X0) (M.op (M.op X5 (M.op X4 X0)) (M.op X0 X2))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X0 X2) (M.op X4 X0) X5 X3
       have i₂ := eq55 X2 X0 X1 X4
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X2 (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X4 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X4 X2) X0)) X2 X4 X1
       have i₂ := eq14 X0 (M.op X4 X2) X3
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) X3))) = (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op (M.op X5 (M.op X1 X2)) X3) X2 X1 X4
       have i₂ := eq55 X3 (M.op X1 X2) X5 X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq561 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq562 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 x
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X3 X0)) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X2) (M.op X3 X0) X4
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0)) = (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X3 X1 X2 (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0))
       have i₂ := eq52 X3 X1 X2 X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) (M.op X3 (M.op (M.op (M.op X4 X2) (M.op X2 X3)) X0)))) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X3 (M.op (M.op (M.op X4 X2) (M.op X2 X3)) X0)) (M.op X2 X3) (M.op X4 X2) X1
       have i₂ := eq52 X3 X4 X2 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op (M.op X5 (M.op (M.op X2 X3) (M.op X3 X4))) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) (M.op (M.op X2 X3) (M.op X3 X4)) X5 X1
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq254 eq50
    | exact resolve eq50 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq121 X1
       grind)
    | exact superpose eq121 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq956 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op X2 y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq935 eq55
    | exact resolve eq55 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1 x
       have i₂ := eq14 (M.op sF0 X0) y x
       grind)
    | exact superpose eq14 eq956
    | exact resolve eq956 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq1002 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq260 eq51
    | exact resolve eq51 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq260
  have eq1066 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq945 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq1135 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1002 eq55
    | exact resolve eq55 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1135 X0 X1 x
       have i₂ := eq14 (M.op sF4 X0) sF3 x
       grind)
    | exact superpose eq14 eq1135
    | exact resolve eq1135 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1203 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq558 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq55 X2 X1 X4 X0
       grind)
    | exact superpose eq55 eq558
    | exact resolve eq558 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq558 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq558 X0 X2 X3
       grind)
    | exact superpose eq558 eq558
    | exact resolve eq558 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq558 (σ X0) X1 (σ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq558
    | exact resolve eq558 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1260 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1203 x X1 X2 X4 X3
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq1203
    | exact resolve eq1203 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1421 : ∀ X1 X2 : G, (M.op y X1) = (M.op (M.op X2 (M.op x (M.op x y))) X1) := by
    intro X1 X2
    first
    | exact superpose eq560 eq1260
    | exact resolve eq1260 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1422 : ∀ X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X2 (M.op (σ x) (M.op (σ x) (σ y)))) X1) := by
    intro X1 X2
    first
    | exact superpose eq561 eq1260
    | exact resolve eq1260 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq10436 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op (M.op (M.op X3 X4) (M.op X4 (M.op X1 X2))) (M.op X2 (M.op X2 X0)))) = (M.op (M.op (M.op X3 X4) (M.op X4 (M.op X1 X2))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq778 (M.op X2 (M.op X2 X0)) X3 X4 (M.op X1 X2)
       have i₂ := eq558 X0 X1 X2
       grind)
    | exact superpose eq558 eq778
    | exact resolve eq778 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10442 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X0 x))) (M.op x (M.op x y)))) = (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X0 x))) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq560 eq778
    | exact resolve eq778 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11061
    | exact resolve eq11061 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11061
  have eq11073 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11062
       have r₂ := eq27
       grind)
    | exact resolve eq11062 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11062
  have eq11077 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11073
    | exact resolve eq11073 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11073
  have eq11079 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11077
    | exact resolve eq11077 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11077
  have eq11081 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11079 eq109
    | (have r₁ := eq109
       have r₂ := eq11079
       grind)
    | exact resolve eq109 eq11079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq11138 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq11081
  have eq11139 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq11138
  have eq13928 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11139 eq96
    | exact resolve eq96 eq11139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq11139
  have eq13945 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13928
  have eq19926 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op y (M.op (M.op X4 y) (M.op (M.op x y) (M.op y X0))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq50 eq542
    | exact resolve eq542 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20344 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X3 X1) (M.op (M.op X4 (M.op X3 X1)) (M.op X1 (M.op (M.op X5 X1) (M.op X1 X2))))) = (M.op (M.op X6 (M.op X3 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq542 X1 x (M.op (M.op X5 X1) (M.op X1 X2)) X6 X3 X4
       have i₂ := eq540 X2 X0 X1 X5 x
       grind)
    | exact superpose eq540 eq542
    | exact resolve eq542 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq542
  have eq20615 : ∀ X0 X1 X2 X3 X6 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X6 (M.op X3 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq20344 X0 X1 X2 X3 x x X6
       have i₂ := eq567 X1 x (M.op X1 X2) X3 x
       grind)
    | exact superpose eq567 eq20344
    | exact resolve eq20344 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq20344
  have eq20715 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19926 X0 X1 X2 X3 x
       have i₂ := eq958 (M.op sF0 (M.op y X0)) X1
       grind)
    | (have i₁ := eq19926 X0 X1 X2 X3 X1
       have i₂ := eq958 (M.op sF0 (M.op y X0)) X1
       grind)
    | exact superpose eq958 eq19926
    | (have j0 := eq19926 X0 X1 X2 X3 x
       grind)
    | exact resolve eq19926 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19926
  have eq20777 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq254 eq20715
    | exact resolve eq20715 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20715
  have eq20800 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq50 eq20777
    | exact resolve eq20777 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq20777
  have eq20802 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20800 X0 X1 X2 X3
       have i₂ := eq958 (M.op (M.op X2 (M.op X1 y)) X0) X1
       grind)
    | (have i₁ := eq20800 X0 x X2 X3
       have i₂ := eq958 (M.op (M.op X2 (M.op x y)) X0) X1
       grind)
    | exact superpose eq958 eq20800
    | exact resolve eq20800 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20800
  have eq21165 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (σ X0)) (M.op (σ X0) (M.op (M.op X2 (σ (M.op X0 X0))) X3))) = (M.op (σ X0) (M.op (M.op X4 (σ (M.op X0 X0))) (M.op (σ (M.op X0 X0)) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq557 X0 (σ X0) (σ X0) X3 X4 x
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq557
    | exact resolve eq557 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21341 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op (M.op X6 (M.op X3 (M.op X0 X1))) X4)) = (M.op (M.op (M.op X5 X0) (M.op X0 X1)) (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 (M.op X0 X1))) (M.op (M.op X3 (M.op X0 X1)) X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq52 X1 X5 X0 (M.op (M.op X0 X1) (M.op (M.op X6 (M.op X3 (M.op X0 X1))) X4))
       have i₂ := eq557 X2 X3 (M.op X0 X1) X4 (M.op X5 X0) X6
       grind)
    | exact superpose eq557 eq52
    | exact resolve eq52 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq21539 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op (M.op X6 (M.op X3 (M.op X0 X1))) X4)) = (M.op X1 (M.op (M.op (M.op X5 X0) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 (M.op X0 X1))) (M.op (M.op X3 (M.op X0 X1)) X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq21341 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq778 (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 (M.op X0 X1))) (M.op (M.op X3 (M.op X0 X1)) X4))) X5 X0 X1
       grind)
    | exact superpose eq778 eq21341
    | exact resolve eq21341 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq21341
  have eq21654 : ∀ X0 X1 X3 X4 X6 : G, (M.op (M.op X0 X1) (M.op (M.op X6 (M.op X3 (M.op X0 X1))) X4)) = (M.op X1 (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X3 X4 X6
    first
    | (have i₁ := eq21539 X0 X1 x X3 X4 x X6
       have i₂ := eq556 X4 (M.op x X0) (M.op X0 X1) x X3
       grind)
    | exact superpose eq556 eq21539
    | exact resolve eq21539 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq21539
  have eq23093 : (k (σ y) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1066 x y
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq1066
    | (have j0 := eq1066 x y
       grind)
    | exact resolve eq1066 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq23122 : (k (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23093
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq23093
    | exact resolve eq23093 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23093
  have eq23184 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23122
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq23122
    | exact resolve eq23122 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23122
  have eq23246 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23184
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23184
    | exact resolve eq23184 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23184
  have eq23299 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23246
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23246
    | exact resolve eq23246 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23246
  have eq23352 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23299
    | exact resolve eq23299 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23299
  have eq23403 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq23352
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23352
    | exact resolve eq23352 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23352
  have eq23448 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq23403
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23403
    | exact resolve eq23403 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23403
  have eq23461 : (k (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23448
    | exact resolve eq23448 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23448
  have eq49525 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq788 X0 X1 X2 X3 X4 x
       have i₂ := eq530 X4 X3 X2 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) x
       grind)
    | exact superpose eq530 eq788
    | exact resolve eq788 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq788
  have eq49526 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49525 X0 X1 X2 X3 X4
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq49525
    | exact resolve eq49525 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq49525
  have eq49642 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op (M.op y (M.op (M.op x y) X0)) (M.op (M.op y X0) X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq254 eq49526
    | exact resolve eq49526 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq49725 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op X1 X0)) X2) = (M.op (M.op X3 (M.op (M.op X4 (M.op X5 X1)) X0)) X2) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq49526 X2 X3 X4 (M.op X5 X1) (M.op X1 (M.op X1 X0))
       have i₂ := eq558 X0 X5 X1
       grind)
    | exact superpose eq558 eq49526
    | exact resolve eq49526 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49888 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op X3 X0) (M.op X0 X1)) X2)) X4) = (M.op (M.op X5 (M.op (M.op X0 X1) X2)) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq49526 X4 X5 x (M.op X0 X1) (M.op X1 (M.op (M.op (M.op X3 X0) (M.op X0 X1)) X2))
       have i₂ := eq782 X2 x X0 X1 X3
       grind)
    | exact superpose eq782 eq49526
    | exact resolve eq49526 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq621716 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49642 X1 X2 X2 X3
       have i₂ := eq20615 y X1 X2 sF0 y
       grind)
    | exact superpose eq20615 eq49642
    | exact resolve eq49642 eq20615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20615 eq49642
  have eq622330 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11079 eq621716
    | exact resolve eq621716 eq11079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624617 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1422 eq622330
    | exact resolve eq622330 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq622330
  have eq1171702 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X5 (M.op (M.op X0 X1) X2)) X4) = (M.op (M.op X1 (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq49888 X0 X1 X2 x X4 X5
       have i₂ := eq49725 X2 X1 X4 X1 (M.op x X0) X0
       grind)
    | exact superpose eq49725 eq49888
    | exact resolve eq49888 eq49725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49725 eq49888
  have eq1658505 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq624617 eq13945
    | exact resolve eq13945 eq624617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13945 eq624617
  have eq1660371 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1658505
  have eq1661306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1660371 eq11079
    | exact resolve eq11079 eq1660371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11079 eq1660371
  have eq1662060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1661306
  have eq1662170 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1662060
       have r₂ := eq27
       grind)
    | exact resolve eq1662060 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662060
  have eq1662225 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq1662170
       grind)
    | exact superpose eq1662170 eq108
    | (have r₁ := eq108
       have r₂ := eq1662170
       grind)
    | exact resolve eq108 eq1662170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1662226 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq1662170
       grind)
    | exact superpose eq1662170 eq120
    | exact resolve eq120 eq1662170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1662570 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x (M.op x y))) X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq621716 x x X0 X1
       have i₂ := eq1662170
       grind)
    | exact superpose eq1662170 eq621716
    | exact resolve eq621716 eq1662170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621716 eq1662170
  have eq1662589 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1662225
  have eq1662590 : (k y x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1662589
  have eq1662592 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1421 eq1662570
    | exact resolve eq1662570 eq1421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421 eq1662570
  have eq1662716 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1662226
    | exact resolve eq1662226 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662226
  have eq1666909 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq1662590
       grind)
    | exact superpose eq1662590 eq74
    | exact resolve eq74 eq1662590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662590
  have eq1789081 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1666909
       have i₂ := eq1662592 x
       grind)
    | exact superpose eq1662592 eq1666909
    | exact resolve eq1666909 eq1662592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662592 eq1666909
  have eq1789243 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1789081
  have eq1789252 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1789243
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq1789243
    | exact resolve eq1789243 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1789243
  have eq1789293 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1789252 eq23461
    | (have r₁ := eq23461
       have r₂ := eq1789252
       grind)
    | exact resolve eq23461 eq1789252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23461 eq1789252
  have eq1789593 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1789293
  have eq1789594 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1789593
  have eq1789777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1789594 eq1662716
    | exact resolve eq1662716 eq1789594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662716 eq1789594
  have eq1790312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1789777
  have eq1790539 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1790312
       have r₂ := eq27
       grind)
    | exact resolve eq1790312 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790312
  have eq1790588 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1790539 eq66
    | (have r₁ := eq66
       have r₂ := eq1790539
       grind)
    | exact resolve eq66 eq1790539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1790597 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1790539 eq1002
    | exact resolve eq1002 eq1790539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1791963 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1790588
  have eq1792117 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1791963 eq92
    | exact resolve eq92 eq1791963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1791963
  have eq1792475 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq1792117
    | exact resolve eq1792117 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1792117
  have eq1792496 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq1792475
       have r₂ := eq65
       grind)
    | exact resolve eq1792475 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1792475
  have eq1792509 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq1792496
       grind)
    | exact superpose eq1792496 eq74
    | exact resolve eq74 eq1792496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792496
  have eq1792577 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1792509
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq1792509
    | exact resolve eq1792509 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq1792509
  have eq1801425 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1790597
    | (have j0 := eq1790597 (σ y)
       grind)
    | exact resolve eq1790597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790597
  have eq1802585 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1790539 eq1801425
    | exact resolve eq1801425 eq1790539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790539 eq1801425
  have eq1803007 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq1802585
  have eq1804582 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1803007 eq558
    | exact resolve eq558 eq1803007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq1803007
  have eq1805130 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1137 eq1804582
    | (have j0 := eq1804582 (σ x)
       grind)
    | exact resolve eq1804582 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804582
  have eq2517339 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op X0 x) (M.op x (M.op x y)))) = (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X0 x))) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10442 X0 X1 x
       have i₂ := eq21654 X0 x x (M.op x sF0) (M.op X1 x)
       grind)
    | exact superpose eq21654 eq10442
    | exact resolve eq10442 eq21654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10442
  have eq2517340 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X0 x))) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2517339 X2 X1 X2
       have i₂ := eq14 sF0 x X2
       grind)
    | exact superpose eq14 eq2517339
    | exact resolve eq2517339 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517339
  have eq3059030 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X4 (M.op X1 X2))) X0) = (M.op X2 (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10436 X0 X1 X2 X3 X4
       have i₂ := eq21654 X1 X2 X4 (M.op X2 (M.op X2 X0)) (M.op X3 X4)
       grind)
    | exact superpose eq21654 eq10436
    | exact resolve eq10436 eq21654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10436 eq21654
  have eq3059031 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op (M.op (M.op X3 X4) (M.op X4 (M.op X1 X2))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3059030 X0 X1 X2 X3 X4
       have i₂ := eq14 (M.op X2 X0) X2 X1
       grind)
    | exact superpose eq14 eq3059030
    | exact resolve eq3059030 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3059030
  have eq3812245 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (σ (k y x))) (M.op (σ (k y x)) (M.op (M.op X1 (M.op (k (σ y) (σ x)) (k (σ y) (σ x)))) X2))) = (M.op (σ (k y x)) (M.op (M.op X3 (M.op (k (σ y) (σ x)) (k (σ y) (σ x)))) (M.op (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21165 (k y x) X1 X2 X3 x
       have i₂ := eq506
       grind)
    | exact superpose eq506 eq21165
    | exact resolve eq21165 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq21165
  have eq3814416 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ (k y x))) (M.op (σ (k y x)) (M.op (M.op X1 (M.op (k (σ y) (σ x)) (k (σ y) (σ x)))) X2))) = (M.op (σ (k y x)) (M.op (k (σ y) (σ x)) (M.op (k (σ y) (σ x)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3812245 X0 X1 X0 X1
       have i₂ := eq1205 X0 X1 (k sF3 sF2) (k sF3 sF2)
       grind)
    | exact superpose eq1205 eq3812245
    | exact resolve eq3812245 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812245
  have eq3815399 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ (k y x))) (M.op (σ (k y x)) (M.op (M.op X1 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) X2))) = (M.op (σ (k y x)) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1792577 eq3814416
    | exact resolve eq3814416 eq1792577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814416
  have eq3815967 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ (k y x))) (M.op (σ (k y x)) (M.op (M.op X1 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) X2))) = (M.op (σ (k y x)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ y)) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1137 eq3815399
    | exact resolve eq3815399 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3815399
  have eq3816265 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ (k y x))) (M.op (σ (k y x)) (M.op (M.op X1 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) X2))) = (M.op (σ (k y x)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1137 eq3815967
    | exact resolve eq3815967 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3815967
  have eq3816410 : ∀ X0 X1 X2 : G, (M.op (k (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X2))) = (M.op (M.op X0 (k (σ y) (σ x))) (M.op (k (σ y) (σ x)) (M.op (M.op X1 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3816265 X0 X1 X2
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq3816265
    | exact resolve eq3816265 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq3816265
  have eq3816490 : ∀ X0 X2 : G, (M.op (M.op X0 (k (σ y) (σ x))) (M.op (k (σ y) (σ x)) (M.op (σ y) X2))) = (M.op (k (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq3816410 X0 x X0
       have i₂ := eq49526 X0 x sF3 sF3 sF3
       grind)
    | exact superpose eq49526 eq3816410
    | exact resolve eq3816410 eq49526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49526 eq3816410
  have eq3816537 : ∀ X0 X2 : G, (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X2))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) X2))) := by
    intro X0 X2
    first
    | exact superpose eq1792577 eq3816490
    | exact resolve eq3816490 eq1792577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792577 eq3816490
  have eq3816551 : ∀ X2 : G, (M.op (σ y) (M.op (σ y) (M.op (σ y) X2))) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X2))) := by
    intro X2
    first
    | (have i₁ := eq3816537 x X2
       have i₂ := eq1205 (M.op sF3 X2) x sF3 sF3
       grind)
    | exact superpose eq1205 eq3816537
    | exact resolve eq3816537 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq3816537
  have eq3816554 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X2))) = (M.op (σ y) (M.op (σ y) (M.op (σ y) X2))) := by
    intro X2
    first
    | exact superpose eq1137 eq3816551
    | exact resolve eq3816551 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816551
  have eq3867778 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) (M.op X1 x))) y) := by
    intro X0 X1
    first
    | exact superpose eq3816554 eq2517340
    | exact resolve eq2517340 eq3816554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517340
  have eq3867784 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) (M.op X3 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3816554 eq3059031
    | exact resolve eq3059031 eq3816554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3059031 eq3816554
  have eq3867816 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X3 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3867784 X0 X1 x X3
       have i₂ := eq1171702 sF4 (M.op sF4 X0) (M.op X3 X1) x (M.op sF3 (M.op sF3 (M.op sF3 X0)))
       grind)
    | exact superpose eq1171702 eq3867784
    | exact resolve eq3867784 eq1171702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3867784
  have eq3867822 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X1 x))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq3867778 X0 X1
       have i₂ := eq1171702 sF4 (M.op sF4 X0) (M.op X1 x) y (M.op sF3 (M.op sF3 (M.op sF3 X0)))
       grind)
    | exact superpose eq1171702 eq3867778
    | exact resolve eq3867778 eq1171702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3867778
  have eq3868556 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X0 (M.op X3 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3867816 X1 X1 x X3
       have i₂ := eq1171702 sF4 X1 (M.op X3 X1) x (M.op sF4 X1)
       grind)
    | exact superpose eq1171702 eq3867816
    | exact resolve eq3867816 eq1171702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3867816
  have eq3868561 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X0 (M.op X1 x))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq3867822 X1 X1
       have i₂ := eq1171702 sF4 X1 (M.op X1 x) y (M.op sF4 X1)
       grind)
    | exact superpose eq1171702 eq3867822
    | exact resolve eq3867822 eq1171702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171702 eq3867822
  have eq3879353 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 (M.op X2 x))) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3868561 X1 X2
       have i₂ := eq1260 (M.op X1 (M.op X2 x)) y X1 X0
       grind)
    | (have i₁ := eq3868561 X1 X2
       have i₂ := eq1260 (M.op X1 (M.op X2 x)) y X0 X1
       grind)
    | exact superpose eq1260 eq3868561
    | exact resolve eq3868561 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868561
  have eq3896126 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op X1 (M.op X1 y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq560 eq3868556
    | exact resolve eq3868556 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq3899637 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3868556 X1 X3 X4 X2
       have i₂ := eq1260 (M.op X1 (M.op X2 X3)) X4 X1 X0
       grind)
    | (have i₁ := eq3868556 X1 X3 X4 X2
       have i₂ := eq1260 (M.op X1 (M.op X2 X3)) X4 X0 X1
       grind)
    | exact superpose eq1260 eq3868556
    | exact resolve eq3868556 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868556
  have eq4038799 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) X2) = (M.op (M.op x (M.op x y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3896126 X2 X1
       have i₂ := eq1260 (M.op X1 y) X2 X1 X0
       grind)
    | (have i₁ := eq3896126 X2 X1
       have i₂ := eq1260 (M.op X1 y) X2 X0 X1
       grind)
    | exact superpose eq1260 eq3896126
    | exact resolve eq3896126 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq3896126
  have eq4053363 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3899637 X2 (M.op x (σ X0)) (σ X0) (σ (M.op X0 X0)) X1
       have i₂ := eq1211 X0 x
       grind)
    | exact superpose eq1211 eq3899637
    | exact resolve eq3899637 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211 eq3899637
  have eq4188034 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq518 X0 x
       have i₂ := eq4053363 X0 (σ (M.op X0 X0)) x
       grind)
    | exact superpose eq4053363 eq518
    | exact resolve eq518 eq4053363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq4053363
  have eq4192602 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4188034 X0
       have i₂ := eq121 (M.op X0 X0)
       grind)
    | exact superpose eq121 eq4188034
    | exact resolve eq4188034 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq4188034
  have eq4258174 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4192602 X0
       have i₂ := eq55 X0 X0 X1 X0
       grind)
    | exact superpose eq55 eq4192602
    | exact resolve eq4192602 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq4192602
  have eq4314612 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op x y) y)) y))))) := by
    intro X0
    first
    | exact superpose eq20802 eq4258174
    | exact resolve eq4258174 eq20802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20802 eq4258174
  have eq4315876 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op x y) y)) y))))) := by
    intro X0
    first
    | (have i₁ := eq4314612 X0
       have i₂ := eq958 (M.op sF0 (M.op (M.op X0 (M.op sF0 y)) y)) sF0
       grind)
    | exact superpose eq958 eq4314612
    | exact resolve eq4314612 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4314612
  have eq4317760 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x (M.op x y)) y))))) := by
    first
    | (have i₁ := eq4315876 x
       have i₂ := eq4038799 x sF0 y
       grind)
    | exact superpose eq4038799 eq4315876
    | exact resolve eq4315876 eq4038799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4038799 eq4315876
  have eq4318796 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ y)) := by
    first
    | (have i₁ := eq4317760
       have i₂ := eq562 sF0 x y
       grind)
    | exact superpose eq562 eq4317760
    | exact resolve eq4317760 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq4317760
  have eq4319306 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ y)) := by
    first
    | (have i₁ := eq4318796
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4318796
    | exact resolve eq4318796 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4318796
  have eq4319746 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq4319306 eq1137
    | exact resolve eq1137 eq4319306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq4320827 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq4319306 eq4319746
    | exact resolve eq4319746 eq4319306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319746
  have eq4324253 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq4320827 eq16
    | exact resolve eq16 eq4320827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4320827
  have eq4324960 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1805130 eq4324253
    | exact resolve eq4324253 eq1805130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805130 eq4324253
  have eq4325397 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq4324960
    | exact resolve eq4324960 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4324960
  have eq4325477 : y = (M.op y (M.op y x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4325397 eq935
    | exact resolve eq935 eq4325397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq4328212 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3879353 X0 y y
       have i₂ := eq4325477
       grind)
    | exact superpose eq4325477 eq3879353
    | exact resolve eq3879353 eq4325477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3879353 eq4325477
  have eq4328894 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4328212 x
       have i₂ := eq958 y x
       grind)
    | (have i₁ := eq4328212 x
       have i₂ := eq958 y x
       grind)
    | exact superpose eq958 eq4328212
    | (have j0 := eq4328212 x
       grind)
    | exact resolve eq4328212 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq4328212
  have eq4329335 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4328894 eq4325397
    | exact resolve eq4325397 eq4328894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4325397 eq4328894
  have eq4329741 : x = (M.op x y) := by grind
  clear eq4329335
  have eq4330493 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4329741 eq20
    | exact resolve eq20 eq4329741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4330857 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4329741 eq4319306
    | exact resolve eq4319306 eq4329741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319306 eq4329741
  have eq4330863 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq4330857
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4330857
    | exact resolve eq4330857 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4330857
  have eq4331071 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4330493
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4330493
    | exact resolve eq4330493 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4330493
  have eq4331074 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq4330863
    | exact resolve eq4330863 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4330863
  have eq4331186 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4331071 eq26
    | exact resolve eq26 eq4331071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4331071
  have eq4335266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4331074 eq4331186
    | exact resolve eq4331186 eq4331074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4331074 eq4331186
  have eq4335267 : False := by grind
  exact eq4335267

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : x ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq91 : ∀ X0 : G, (σ (k (k y x) X0)) = (k (k (σ y) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k y x) X0
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq10
    | exact resolve eq10 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq109 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq111 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq112 (σ X0)
       grind)
    | exact superpose eq112 eq10
    | exact resolve eq10 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq43
    | exact resolve eq43 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq116 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq75
    | exact resolve eq75 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq119 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq116
    | exact resolve eq116 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq115
    | exact resolve eq115 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq114
    | exact resolve eq114 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq128 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq101
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq101
    | exact resolve eq101 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq128
    | exact resolve eq128 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq254 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq14
    | exact resolve eq14 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X4 (M.op (M.op X2 X1) (M.op X1 X0))) X3)) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op (M.op X2 X1) (M.op X1 X0)) X4 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X1) X2) (M.op (M.op X5 (M.op (M.op X3 X1) X2)) X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op (M.op X3 X1) X2) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 (M.op (M.op X3 X1) X2) X5 X1
       have i₂ := eq55 X2 X1 X3 X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X2) (M.op (M.op X5 (M.op X0 X2)) X4)) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 X2) X4)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq55 X4 (M.op X0 X2) X5 (M.op x X0)
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X3 X2) (M.op X2 X0)))) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X3 X2) (M.op X2 X0)) X2 X4 X1
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X0) (M.op (M.op X5 (M.op X4 X0)) (M.op X0 X2))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X0 X2) (M.op X4 X0) X5 X3
       have i₂ := eq55 X2 X0 X1 X4
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op (M.op X0 X2) X4)) = (M.op (M.op X0 X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X4 (M.op X0 X2) (M.op x X0) X3
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X2 (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X4 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X4 X2) X0)) X2 X4 X1
       have i₂ := eq14 X0 (M.op X4 X2) X3
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq562 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 x
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X3 X0)) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X2) (M.op X3 X0) X4
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op (M.op X5 (M.op (M.op X2 X3) (M.op X3 X4))) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) (M.op (M.op X2 X3) (M.op X3 X4)) X5 X1
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq254 eq50
    | exact resolve eq50 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op X2 y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq935 eq55
    | exact resolve eq55 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1 x
       have i₂ := eq14 (M.op sF0 X0) y x
       grind)
    | exact superpose eq14 eq956
    | exact resolve eq956 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq1003 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq260 eq51
    | exact resolve eq51 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1137 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1003 eq55
    | exact resolve eq55 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1139 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1137 X0 X1 x
       have i₂ := eq14 (M.op sF4 X0) sF3 x
       grind)
    | exact superpose eq14 eq1137
    | exact resolve eq1137 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1192 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq558 X1 (σ X0) (σ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq558
    | exact resolve eq558 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1206 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq558 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq55 X2 X1 X4 X0
       grind)
    | exact superpose eq55 eq558
    | exact resolve eq558 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq558 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq558 X0 X2 X3
       grind)
    | exact superpose eq558 eq558
    | exact resolve eq558 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1214 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq558 (σ X0) X1 (σ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq558
    | exact resolve eq558 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1263 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1206 x X1 X2 X4 X3
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq1206
    | exact resolve eq1206 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1424 : ∀ X1 X2 : G, (M.op y X1) = (M.op (M.op X2 (M.op x (M.op x y))) X1) := by
    intro X1 X2
    first
    | exact superpose eq560 eq1263
    | exact resolve eq1263 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1425 : ∀ X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X2 (M.op (σ x) (M.op (σ x) (σ y)))) X1) := by
    intro X1 X2
    first
    | exact superpose eq561 eq1263
    | exact resolve eq1263 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq4655 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op X0 (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq260 eq265
    | exact resolve eq265 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq4719 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq273 X0 (M.op sF4 (M.op sF4 X0))
       have i₂ := eq558 X0 (M.op X0 sF2) sF4
       grind)
    | exact superpose eq558 eq273
    | exact resolve eq273 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq7578 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op x y) (M.op y (M.op (M.op X1 (M.op X2 y)) (M.op (M.op X2 y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq556 X0 x y X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq556
    | (have j0 := eq556 X0 x y X1 X2
       grind)
    | exact resolve eq556 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq7838 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X2 y)) (M.op (M.op X2 y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq254 eq7578
    | exact resolve eq7578 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7578
  have eq7864 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X2 y)) (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7838 X0 X1 X2
       have i₂ := eq958 X0 X2
       grind)
    | (have i₁ := eq7838 X0 X1 x
       have i₂ := eq958 X0 X1
       grind)
    | exact superpose eq958 eq7838
    | exact resolve eq7838 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7838
  have eq7888 : ∀ X0 X2 X3 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op X3 (M.op (σ x) (M.op (σ x) (σ y)))) X0)))) := by
    intro X0 X2 X3
    first
    | exact superpose eq561 eq567
    | exact resolve eq567 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq7930 : ∀ X0 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op x (M.op x y)) (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op x y)) X0)))) := by
    intro X0 X2
    first
    | exact superpose eq560 eq567
    | exact resolve eq567 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8185 : ∀ X0 X3 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op X3 (M.op (σ x) (M.op (σ x) (σ y)))) X0)))) := by
    intro X0 X3
    first
    | exact superpose eq1139 eq7888
    | (have j0 := eq7888 X0 (σ x) X3
       grind)
    | exact resolve eq7888 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7888
  have eq8195 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq1425 eq8185
    | exact resolve eq8185 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425 eq8185
  have eq10765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10765
    | exact resolve eq10765 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10765
  have eq10777 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10766
       have r₂ := eq27
       grind)
    | exact resolve eq10766 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10766
  have eq10781 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10777
    | exact resolve eq10777 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10777
  have eq10783 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10781
    | exact resolve eq10781 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10781
  have eq10785 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10783 eq109
    | (have r₁ := eq109
       have r₂ := eq10783
       grind)
    | exact resolve eq109 eq10783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq10783
  have eq10839 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq10785
  have eq10840 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq10839
  have eq11839 : ∀ X0 X1 : G, (M.op y (M.op (M.op x (M.op x y)) X1)) = (M.op (M.op x (M.op x y)) (M.op (M.op X0 (M.op x (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq532
    | exact resolve eq532 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq532
  have eq12120 : ∀ X1 : G, (M.op y (M.op (M.op x (M.op x y)) X1)) = (M.op (M.op x (M.op x y)) (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq1424 eq11839
    | exact resolve eq11839 eq1424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11839
  have eq12910 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op (M.op x (M.op x (M.op x y))) X1)) = (M.op (M.op x (M.op x (M.op x y))) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq560 eq553
    | exact resolve eq553 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq560
  have eq13185 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X1)) = (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op (M.op x (M.op x (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1424 eq12910
    | exact resolve eq12910 eq1424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12910
  have eq13242 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X1)) = (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq1424 eq13185
    | exact resolve eq13185 eq1424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424 eq13185
  have eq13265 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X1)) = (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13242 X0 X1
       have i₂ := eq958 X1 x
       grind)
    | (have i₁ := eq13242 X0 X0
       have i₂ := eq958 X0 X1
       grind)
    | exact superpose eq958 eq13242
    | (have j0 := eq13242 X0 X1
       grind)
    | exact resolve eq13242 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13242
  have eq20540 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op y (M.op (M.op X4 y) (M.op (M.op x y) (M.op y X0))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq50 eq542
    | exact resolve eq542 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20990 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X3 X1) (M.op (M.op X4 (M.op X3 X1)) (M.op X1 (M.op (M.op X5 X1) (M.op X1 X2))))) = (M.op (M.op X6 (M.op X3 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq542 X1 x (M.op (M.op X5 X1) (M.op X1 X2)) X6 X3 X4
       have i₂ := eq540 X2 X0 X1 X5 x
       grind)
    | exact superpose eq540 eq542
    | exact resolve eq542 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq21262 : ∀ X0 X1 X2 X3 X6 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X6 (M.op X3 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq20990 X0 X1 X2 X3 x x X6
       have i₂ := eq567 X1 x (M.op X1 X2) X3 x
       grind)
    | exact superpose eq567 eq20990
    | exact resolve eq20990 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq20990
  have eq21400 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20540 X0 X1 X2 X3 x
       have i₂ := eq958 (M.op sF0 (M.op y X0)) X1
       grind)
    | (have i₁ := eq20540 X0 X1 X2 X3 X1
       have i₂ := eq958 (M.op sF0 (M.op y X0)) X1
       grind)
    | exact superpose eq958 eq20540
    | (have j0 := eq20540 X0 X1 X2 X3 x
       grind)
    | exact resolve eq20540 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20540
  have eq21494 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq254 eq21400
    | exact resolve eq21400 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21400
  have eq21520 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq50 eq21494
    | exact resolve eq21494 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq21494
  have eq21522 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21520 X0 X1 X2 X3
       have i₂ := eq958 (M.op (M.op X2 (M.op X1 y)) X0) X1
       grind)
    | (have i₁ := eq21520 X0 x X2 X3
       have i₂ := eq958 (M.op (M.op X2 (M.op x y)) X0) X1
       grind)
    | exact superpose eq958 eq21520
    | exact resolve eq21520 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21520
  have eq28673 : ∀ X0 X1 X2 X3 X4 X5 X7 : G, (M.op (M.op X7 (M.op (M.op X3 X1) X2)) X5) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op (M.op X3 X1) X2) (M.op (M.op X4 (M.op (M.op X3 X1) X2)) (M.op (M.op (M.op X3 X1) X2) X5)))) := by
    intro X0 X1 X2 X3 X4 X5 X7
    first
    | (have i₁ := eq540 X5 X7 (M.op (M.op X3 X1) X2) X4 x
       have i₂ := eq531 X0 X1 X2 X3 (M.op (M.op X4 (M.op (M.op X3 X1) X2)) (M.op (M.op (M.op X3 X1) X2) X5)) x
       grind)
    | exact superpose eq531 eq540
    | exact resolve eq540 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq28881 : ∀ X0 X1 X2 X3 X5 X7 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X5) = (M.op (M.op X7 (M.op (M.op X3 X1) X2)) X5) := by
    intro X0 X1 X2 X3 X5 X7
    first
    | (have i₁ := eq28673 X0 X1 X2 X3 x X5 X7
       have i₂ := eq14 X5 (M.op (M.op X3 X1) X2) x
       grind)
    | exact superpose eq14 eq28673
    | exact resolve eq28673 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28673
  have eq39164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10840 eq96
    | exact resolve eq96 eq10840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq10840
  have eq39188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq39164
  have eq39192 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq39188
       have r₂ := eq27
       grind)
    | exact resolve eq39188 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39188
  have eq39885 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq39192
       grind)
    | exact superpose eq39192 eq108
    | (have r₁ := eq108
       have r₂ := eq39192
       grind)
    | exact resolve eq108 eq39192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq39886 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq39192
       grind)
    | exact superpose eq39192 eq120
    | exact resolve eq120 eq39192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq39192
  have eq39991 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq39885
  have eq39992 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq39991
  have eq40003 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq39886
    | exact resolve eq39886 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39886
  have eq40437 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq39992
       grind)
    | exact superpose eq39992 eq74
    | exact resolve eq74 eq39992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39992
  have eq40468 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq40437
    | exact resolve eq40437 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40437
  have eq41074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40468 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq40468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40468
  have eq41079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq41074
    | exact resolve eq41074 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41074
  have eq41090 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41079
       have r₂ := eq27
       grind)
    | exact resolve eq41079 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41079
  have eq41094 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq41090
    | exact resolve eq41090 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41090
  have eq41096 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq41094
    | exact resolve eq41094 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41094
  have eq41097 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq41096
  have eq41119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41097 eq40003
    | exact resolve eq40003 eq41097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40003 eq41097
  have eq41232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41119
  have eq41249 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq41232
       have r₂ := eq27
       grind)
    | exact resolve eq41232 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41232
  have eq41636 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41249 eq66
    | (have r₁ := eq66
       have r₂ := eq41249
       grind)
    | exact resolve eq66 eq41249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq41644 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41249 eq1003
    | exact resolve eq1003 eq41249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq41728 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq41636
  have eq42580 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41728 eq92
    | exact resolve eq92 eq41728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq41728
  have eq42611 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq42580
    | exact resolve eq42580 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq42580
  have eq42614 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq42611
       have r₂ := eq65
       grind)
    | exact resolve eq42611 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq42611
  have eq42621 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq42614
       grind)
    | exact superpose eq42614 eq74
    | exact resolve eq74 eq42614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq42646 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq42621
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq42621
    | exact resolve eq42621 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42621
  have eq42684 : ∀ X0 : G, (σ (k (k y x) X0)) = (k (M.op (σ y) (σ y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq42646 eq91
    | exact resolve eq91 eq42646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq42646
  have eq42709 : ∀ X0 : G, (σ (k (M.op y y) X0)) = (k (M.op (σ y) (σ y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq42684 X0
       have i₂ := eq42614
       grind)
    | exact superpose eq42614 eq42684
    | exact resolve eq42684 eq42614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42614 eq42684
  have eq47968 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq41644
    | (have j0 := eq41644 (σ y)
       grind)
    | exact resolve eq41644 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41644
  have eq48171 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41249 eq47968
    | exact resolve eq47968 eq41249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41249 eq47968
  have eq48285 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq48171
  have eq50013 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq788 X0 X1 X2 X3 X4 x
       have i₂ := eq530 X4 X3 X2 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) x
       grind)
    | exact superpose eq530 eq788
    | exact resolve eq788 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq788
  have eq50014 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50013 X0 X1 X2 X3 X4
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq50013
    | exact resolve eq50013 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq50013
  have eq50404 : ∀ X0 X1 X2 X3 X5 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X0 (M.op (M.op X5 (M.op X5 X0)) X1))) X2) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq50014 X2 X3 (M.op x X5) (M.op X5 (M.op X5 X0)) X1
       have i₂ := eq558 X0 x X5
       grind)
    | exact superpose eq558 eq50014
    | exact resolve eq50014 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50014
  have eq51524 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq48285 eq558
    | exact resolve eq558 eq48285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq48285
  have eq51667 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1139 eq51524
    | (have j0 := eq51524 (σ x)
       grind)
    | exact resolve eq51524 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51524
  have eq78219 : (σ (k (M.op y y) (M.op y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq42709 (M.op y y)
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq42709
    | exact resolve eq42709 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42709
  have eq78355 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq78219
       have i₂ := eq112 (M.op sF3 sF3)
       grind)
    | exact superpose eq112 eq78219
    | exact resolve eq78219 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78219
  have eq78374 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq78355
       have i₂ := eq112 (M.op y y)
       grind)
    | exact superpose eq112 eq78355
    | exact resolve eq78355 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq78355
  have eq78379 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1139 eq78374
    | exact resolve eq78374 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78374
  have eq78382 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq260 eq78379
    | exact resolve eq78379 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq78379
  have eq78385 : (σ (M.op (M.op x y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq78382
       have i₂ := eq958 (M.op y y) y
       grind)
    | exact superpose eq958 eq78382
    | exact resolve eq78382 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78382
  have eq78388 : (σ (M.op y (M.op (M.op x y) y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq254 eq78385
    | exact resolve eq78385 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78385
  have eq109525 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) (M.op y y))) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1192 (M.op y y) x
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq1192
    | exact resolve eq1192 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq1192
  have eq109786 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) (M.op y y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1139 eq109525
    | exact resolve eq109525 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109525
  have eq109820 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) (M.op y y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1139 eq109786
    | exact resolve eq109786 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109786
  have eq109832 : ∀ X0 : G, (M.op (σ (M.op (M.op x y) (M.op y y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq109820 X0
       have i₂ := eq958 (M.op y y) y
       grind)
    | exact superpose eq958 eq109820
    | exact resolve eq109820 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109820
  have eq109841 : ∀ X0 : G, (M.op (σ (M.op y (M.op (M.op x y) y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq254 eq109832
    | exact resolve eq109832 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq109832
  have eq109848 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq78388 eq109841
    | exact resolve eq109841 eq78388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78388 eq109841
  have eq109956 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq109848 (M.op (M.op X1 sF4) x)
       have i₂ := eq562 sF4 X1 x
       grind)
    | exact superpose eq562 eq109848
    | exact resolve eq109848 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109848
  have eq140575 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq109956 eq4719
    | exact resolve eq4719 eq109956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719 eq109956
  have eq140651 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0
    first
    | exact superpose eq140575 eq4655
    | exact resolve eq4655 eq140575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655
  have eq140910 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0
    first
    | exact superpose eq140575 eq140651
    | exact resolve eq140651 eq140575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140575 eq140651
  have eq141219 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq140910 (M.op (M.op X1 sF4) x)
       have i₂ := eq562 sF4 X1 x
       grind)
    | exact superpose eq562 eq140910
    | exact resolve eq140910 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142192 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ y) (M.op (M.op X1 (σ y)) (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))))) = (M.op (M.op X4 (σ y)) (M.op (M.op X3 (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq141219 eq540
    | exact resolve eq540 eq141219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141219
  have eq142309 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 (M.op (σ x) (σ y))) X0)) = (M.op (σ y) (M.op (M.op X1 (σ y)) (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1139 eq142192
    | (have j0 := eq142192 X0 X1 X2 X3 (σ x)
       grind)
    | exact resolve eq142192 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142192
  have eq142359 : ∀ X0 X2 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 (M.op (σ x) (σ y))) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq1139 eq142309
    | (have j0 := eq142309 X0 (σ x) X2 X3
       grind)
    | exact resolve eq142309 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142309
  have eq142380 : ∀ X0 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 (M.op (σ x) (σ y))) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X3
    first
    | exact superpose eq1139 eq142359
    | (have j0 := eq142359 X0 (σ x) X3
       grind)
    | exact resolve eq142359 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142359
  have eq142388 : ∀ X0 X3 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 (M.op (σ x) (σ y))) X0)) := by
    intro X0 X3
    first
    | exact superpose eq140910 eq142380
    | exact resolve eq142380 eq140910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140910 eq142380
  have eq210826 : ∀ X0 X2 : G, (M.op (M.op x y) X0) = (M.op y (M.op (M.op x (M.op x y)) (M.op (M.op x y) (M.op (M.op X2 (M.op x y)) X0)))) := by
    intro X0 X2
    first
    | exact superpose eq12120 eq7930
    | exact resolve eq7930 eq12120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7930 eq12120
  have eq219906 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq142388 eq8195
    | exact resolve eq8195 eq142388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8195 eq142388
  have eq262776 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op (M.op (σ y) (M.op (σ y) X0)) (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq219906 eq50404
    | exact resolve eq50404 eq219906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50404 eq219906
  have eq264234 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq262776 X1 X2 X2 X3
       have i₂ := eq21262 (M.op sF2 sF4) X1 X2 sF3 sF3
       grind)
    | exact superpose eq21262 eq262776
    | exact resolve eq262776 eq21262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21262 eq262776
  have eq293423 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op x (M.op x y)) (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) X0))))) = (M.op (M.op X2 (M.op x (M.op x (M.op x y)))) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq210826 eq13265
    | exact resolve eq13265 eq210826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13265 eq210826
  have eq293706 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op y (M.op (M.op x y) (M.op (M.op x (M.op x y)) (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq293423 X0 X1 x
       have i₂ := eq264234 x sF0 (M.op sF0 X0) x
       grind)
    | exact superpose eq264234 eq293423
    | exact resolve eq293423 eq264234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293423
  have eq293851 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X1 (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq293706 X0 X1
       have i₂ := eq14 (M.op (M.op X1 sF0) X0) sF0 x
       grind)
    | exact superpose eq14 eq293706
    | exact resolve eq293706 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293706
  have eq294090 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op (M.op X2 (M.op X1 (M.op x y))) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq293851 (M.op (M.op X1 sF0) (M.op (M.op X1 (M.op X1 sF0)) X2)) X1
       have i₂ := eq562 (M.op X1 sF0) X1 X2
       grind)
    | exact superpose eq562 eq293851
    | exact resolve eq293851 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293851
  have eq294415 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op X2 (M.op X1 (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq294090 X0 X1 X2
       have i₂ := eq562 sF0 X1 (M.op (M.op X2 (M.op X1 sF0)) X0)
       grind)
    | exact superpose eq562 eq294090
    | exact resolve eq294090 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294090
  have eq294847 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op (M.op X1 (M.op x y)) (M.op y X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq294415 eq562
    | exact resolve eq562 eq294415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq294415
  have eq296700 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op (M.op X2 (M.op X3 y)) (M.op (M.op x y) X0))) = (M.op (M.op X1 (M.op x y)) (M.op (M.op X1 (M.op x y)) (M.op y X0))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq7864 eq294847
    | exact resolve eq294847 eq7864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7864
  have eq297085 : ∀ X0 X2 X3 : G, (M.op (M.op x y) (M.op (M.op X2 (M.op X3 y)) (M.op (M.op x y) X0))) = X0 := by
    intro X0 X2 X3
    first
    | exact superpose eq294847 eq296700
    | exact resolve eq296700 eq294847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294847 eq296700
  have eq301621 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op (M.op X1 (M.op X0 y)) (M.op (M.op X2 (M.op X0 y)) (M.op (M.op X0 y) (M.op (M.op x y) X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq297085 X0 X1 X3
       have i₂ := eq540 (M.op sF0 X0) X1 (M.op X3 y) X3 x
       grind)
    | exact superpose eq540 eq297085
    | exact resolve eq297085 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq297085
  have eq301875 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op X0 y)) (M.op (M.op X2 (M.op X0 y)) (M.op (M.op X0 y) (M.op (M.op x y) X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq301621 x X1 X2 X3
       have i₂ := eq958 (M.op (M.op X1 (M.op x y)) (M.op (M.op X2 (M.op x y)) (M.op (M.op x y) (M.op sF0 X3)))) X1
       grind)
    | (have i₁ := eq301621 X1 X1 X2 X3
       have i₂ := eq958 (M.op (M.op X1 (M.op X1 y)) (M.op (M.op X2 (M.op X1 y)) (M.op (M.op X1 y) (M.op sF0 X3)))) X1
       grind)
    | exact superpose eq958 eq301621
    | exact resolve eq301621 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301621
  have eq301914 : ∀ X0 X1 X3 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op X0 y)) (M.op y (M.op y (M.op (M.op x y) X3)))))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq301875 x X1 X1 X3
       have i₂ := eq1208 (M.op sF0 X3) X1 x y
       grind)
    | exact superpose eq1208 eq301875
    | exact resolve eq301875 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208 eq301875
  have eq301924 : ∀ X0 X1 X3 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op X0 y)) X3))) = X3 := by
    intro X0 X1 X3
    first
    | exact superpose eq935 eq301914
    | exact resolve eq301914 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq301914
  have eq560746 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (σ X0)) X2) = (M.op (M.op (M.op X1 (σ X0)) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28881 X1 (σ X0) (M.op (σ X0) (σ (M.op X0 X0))) x X2 X3
       have i₂ := eq1214 X0 x
       grind)
    | exact superpose eq1214 eq28881
    | exact resolve eq28881 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214 eq28881
  have eq564083 : ∀ X0 X2 X3 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (M.op X3 (σ X0)) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq560746 X0 x X2 X3
       have i₂ := eq264234 (σ X0) (σ (M.op X0 X0)) X2 (M.op x (σ X0))
       grind)
    | exact superpose eq264234 eq560746
    | exact resolve eq560746 eq264234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264234 eq560746
  have eq568637 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq518 X0 x
       have i₂ := eq564083 X0 (σ (M.op X0 X0)) x
       grind)
    | exact superpose eq564083 eq518
    | exact resolve eq518 eq564083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq564083
  have eq569452 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq568637 X0
       have i₂ := eq121 (M.op X0 X0)
       grind)
    | exact superpose eq121 eq568637
    | exact resolve eq568637 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq568637
  have eq570087 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq569452 X0
       have i₂ := eq55 X0 X0 X1 X0
       grind)
    | exact superpose eq55 eq569452
    | exact resolve eq569452 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq569452
  have eq579042 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op x y) y)) y))))) := by
    intro X0
    first
    | exact superpose eq21522 eq570087
    | exact resolve eq570087 eq21522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21522 eq570087
  have eq579500 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op x y) y)) y))))) := by
    intro X0
    first
    | (have i₁ := eq579042 X0
       have i₂ := eq958 (M.op sF0 (M.op (M.op X0 (M.op sF0 y)) y)) sF0
       grind)
    | exact superpose eq958 eq579042
    | exact resolve eq579042 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579042
  have eq580023 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ y)) := by
    first
    | (have i₁ := eq579500 x
       have i₂ := eq301924 x x (M.op sF0 (M.op sF0 (M.op (M.op x (M.op sF0 y)) y)))
       grind)
    | exact superpose eq301924 eq579500
    | exact resolve eq579500 eq301924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301924 eq579500
  have eq580281 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ y)) := by
    first
    | (have i₁ := eq580023
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq580023
    | exact resolve eq580023 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq580023
  have eq580469 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq580281 eq1139
    | exact resolve eq1139 eq580281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq580862 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq580281 eq580469
    | exact resolve eq580469 eq580281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580469
  have eq581928 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq580862 eq16
    | exact resolve eq16 eq580862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580862
  have eq582879 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51667 eq581928
    | exact resolve eq581928 eq51667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51667 eq581928
  have eq583103 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq582879
    | exact resolve eq582879 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq582879
  have eq583151 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq583103 eq958
    | exact resolve eq958 eq583103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq600912 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq583151 eq583103
    | exact resolve eq583103 eq583151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583103 eq583151
  have eq601793 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq600912
  have eq601918 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq601793
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq601793
    | exact resolve eq601793 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601793
  have eq601919 : x = (M.op x y) := by grind
  clear eq601918
  have eq602072 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq601919 eq20
    | exact resolve eq20 eq601919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602290 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq601919 eq580281
    | exact resolve eq580281 eq601919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580281 eq601919
  have eq602298 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq602290
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq602290
    | exact resolve eq602290 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq602290
  have eq602444 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq602072
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq602072
    | exact resolve eq602072 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq602072
  have eq602448 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq602298
    | exact resolve eq602298 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq602298
  have eq602503 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq602444 eq26
    | exact resolve eq26 eq602444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq602444
  have eq604039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq602448 eq602503
    | exact resolve eq602503 eq602448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602448 eq602503
  have eq604040 : False := by grind
  exact eq604040

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  clear eq36
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq55 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq107
    | (have j0 := eq107 (σ X0)
       grind)
    | exact resolve eq107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq44
    | (have j1 := eq107 x
       grind)
    | exact resolve eq44 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq468 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X4 (M.op (M.op X2 X1) (M.op X1 X0))) X3)) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X3 (M.op (M.op X2 X1) (M.op X1 X0)) X4 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq496 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq497 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 x
       have i₂ := eq56 X2 X0 X1 x
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X1 : G, (M.op (M.op x (M.op x y)) (M.op y (M.op (M.op x (M.op x y)) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq495 eq14
    | exact resolve eq14 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq496 eq14
    | exact resolve eq14 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op (M.op X5 (M.op (M.op X2 X3) (M.op X3 X4))) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) (M.op (M.op X2 X3) (M.op X3 X4)) X5 X1
       have i₂ := eq53 X4 X2 X3 X0
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq493 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq56 X2 X1 X4 X0
       grind)
    | exact superpose eq56 eq493
    | exact resolve eq493 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq974 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq918 x X1 X2 X4 X3
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq918
    | exact resolve eq918 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq6164 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq13547 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) (M.op y (M.op (M.op X0 (M.op x y)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq516 x
       have i₂ := eq974 sF0 x x x
       grind)
    | (have i₁ := eq516 x
       have i₂ := eq974 sF0 x x x
       grind)
    | exact superpose eq974 eq516
    | exact resolve eq516 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq13652 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq528 x
       have i₂ := eq974 sF4 x sF2 x
       grind)
    | (have i₁ := eq528 x
       have i₂ := eq974 sF4 x x sF2
       grind)
    | exact superpose eq974 eq528
    | exact resolve eq528 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq974
  have eq27891 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X1 (M.op x y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq13547 eq497
    | exact resolve eq497 eq13547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13547
  have eq29484 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq13652 eq497
    | exact resolve eq497 eq13652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13652
  have eq50002 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op (M.op X2 (M.op X1 (M.op x y))) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27891 (M.op (M.op X1 sF0) (M.op (M.op X1 (M.op X1 sF0)) X2)) X1
       have i₂ := eq497 (M.op X1 sF0) X1 X2
       grind)
    | exact superpose eq497 eq27891
    | exact resolve eq27891 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27891
  have eq50167 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op X2 (M.op X1 (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50002 X0 X1 X2
       have i₂ := eq497 sF0 X1 (M.op (M.op X2 (M.op X1 sF0)) X0)
       grind)
    | exact superpose eq497 eq50002
    | exact resolve eq50002 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50002
  have eq50259 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq569 X0 X1 X2 X3 X4 x
       have i₂ := eq468 X4 X3 X2 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) x
       grind)
    | exact superpose eq468 eq569
    | exact resolve eq569 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq569
  have eq50260 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50259 X0 X1 X2 X3 X4
       have i₂ := eq53 X4 X2 X3 X0
       grind)
    | exact superpose eq53 eq50259
    | exact resolve eq50259 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq50259
  have eq58299 : ∀ X0 X1 X2 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29484 (M.op (M.op X1 sF4) (M.op (M.op X1 (M.op X1 sF4)) X2)) X1
       have i₂ := eq497 (M.op X1 sF4) X1 X2
       grind)
    | exact superpose eq497 eq29484
    | exact resolve eq29484 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29484
  have eq58479 : ∀ X0 X1 X2 : G, (M.op (σ y) X0) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58299 X0 X1 X2
       have i₂ := eq497 sF4 X1 (M.op (M.op X2 (M.op X1 sF4)) X0)
       grind)
    | exact superpose eq497 eq58299
    | exact resolve eq58299 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq58299
  have eq66193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq66193
    | exact resolve eq66193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66193
  have eq66205 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq66194
       have r₂ := eq28
       grind)
    | exact resolve eq66194 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66194
  have eq66207 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq66205
    | exact resolve eq66205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66205
  have eq66315 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (σ x) (σ y)))) X0) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | exact superpose eq66207 eq50260
    | exact resolve eq50260 eq66207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66317 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq58479 eq66315
    | exact resolve eq66315 eq58479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58479 eq66315
  have eq67545 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq66317 eq66207
    | exact resolve eq66207 eq66317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66207 eq66317
  have eq67790 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq67545
  have eq68235 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq67790 eq493
    | exact resolve eq493 eq67790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67790
  have eq68302 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq496 eq68235
    | exact resolve eq68235 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq68235
  have eq68331 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq68302
  have eq68455 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq68331
    | exact resolve eq68331 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68331
  have eq68501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq68455 eq95
    | exact resolve eq95 eq68455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq68455
  have eq68509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq68501
  have eq68511 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq68509
       have r₂ := eq28
       grind)
    | exact resolve eq68509 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68509
  have eq68619 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op X1 (M.op (M.op X2 y) (M.op x y))) X0) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50260 X0 X1 X2 y x
       have i₂ := eq68511
       grind)
    | exact superpose eq68511 eq50260
    | exact resolve eq50260 eq68511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50260
  have eq68621 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq50167 eq68619
    | exact resolve eq68619 eq50167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50167 eq68619
  have eq70708 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68511
       have i₂ := eq68621 x
       grind)
    | exact superpose eq68621 eq68511
    | exact resolve eq68511 eq68621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68511 eq68621
  have eq70957 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq70708
  have eq71154 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq493 x X0 x
       have i₂ := eq70957
       grind)
    | exact superpose eq70957 eq493
    | exact resolve eq493 eq70957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq70957
  have eq71221 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq495 eq71154
    | exact resolve eq71154 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq71154
  have eq71486 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq380
       have i₂ := eq71221
       grind)
    | exact superpose eq71221 eq380
    | exact resolve eq380 eq71221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71500 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq71221
  have eq71595 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq71486
  have eq71625 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71500
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq71500
    | exact resolve eq71500 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71500
  have eq71629 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71595
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq71595
    | exact resolve eq71595 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71595
  have eq71923 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq71625
       grind)
    | exact superpose eq71625 eq72
    | exact resolve eq72 eq71625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq71625
  have eq71941 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq71923
    | exact resolve eq71923 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71923
  have eq71942 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq71629
       have i₂ := eq107 sF2
       grind)
    | exact superpose eq107 eq71629
    | (have j1 := eq107 (σ x)
       grind)
    | exact resolve eq71629 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104402 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq71942
  have eq104557 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq104402
    | exact resolve eq104402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104402
  have eq104832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq104557 eq71941
    | exact resolve eq71941 eq104557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71941 eq104557
  have eq104836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq104832
  have eq104845 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq104836
       have r₂ := eq28
       grind)
    | exact resolve eq104836 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104836
  have eq104868 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq105362 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq104868 eq71629
    | exact resolve eq71629 eq104868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71629 eq104868
  have eq105376 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq105362
  have eq105386 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq105376 eq104845
    | exact resolve eq104845 eq105376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104845 eq105376
  have eq105509 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq105386
  have eq105594 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq105509 eq30
    | exact resolve eq30 eq105509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq105509
  have eq105759 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq105594
    | exact resolve eq105594 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq105594
  have eq105760 : x = y := by grind
  clear eq105759
  have eq105764 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq105760
       grind)
    | exact superpose eq105760 eq19
    | exact resolve eq19 eq105760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq105765 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq105760
       grind)
    | exact superpose eq105760 eq25
    | exact resolve eq25 eq105760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq105760
  have eq105936 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq105765
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq105765
    | exact resolve eq105765 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105765
  have eq105937 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq105936 eq27
    | exact resolve eq27 eq105936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq105936
  have eq106114 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq380
       have i₂ := eq105764
       grind)
    | exact superpose eq105764 eq380
    | exact resolve eq380 eq105764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq106146 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq106304 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq106114
    | exact resolve eq106114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106114
  have eq106353 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq110155 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106304 eq107
    | (have j0 := eq107 (σ x)
       grind)
    | exact resolve eq107 eq106304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105937 eq110155
    | exact resolve eq110155 eq105937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110155
  have eq110168 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq110156
       have r₂ := eq28
       grind)
    | exact resolve eq110156 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110156
  have eq110174 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105937 eq110168
    | exact resolve eq110168 eq105937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110168
  have eq110228 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110174 eq106353
    | exact resolve eq106353 eq110174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106353 eq110174
  have eq110233 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105937 eq110228
    | exact resolve eq110228 eq105937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110228
  have eq111879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110233 eq106304
    | exact resolve eq106304 eq110233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106304 eq110233
  have eq111883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq111879
  have eq111887 : x = (M.op x y) := by
    first
    | (have r₁ := eq111883
       have r₂ := eq28
       grind)
    | exact resolve eq111883 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111883
  have eq111895 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq111887 eq21
    | exact resolve eq21 eq111887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq112049 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq111887 eq106146
    | exact resolve eq106146 eq111887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106146
  have eq112056 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq112049
       have i₂ := eq105764
       grind)
    | exact superpose eq105764 eq112049
    | exact resolve eq112049 eq105764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105764 eq112049
  have eq112161 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq111895
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq111895
    | exact resolve eq111895 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111895
  have eq112165 : x = (k x x) := by
    first
    | exact superpose eq111887 eq112056
    | exact resolve eq112056 eq111887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111887 eq112056
  have eq112574 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6164 x
       have i₂ := eq112165
       grind)
    | exact superpose eq112165 eq6164
    | (have j0 := eq6164 x
       grind)
    | exact resolve eq6164 eq112165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6164 eq112165
  have eq112578 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq112574
  have eq112588 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq112578
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq112578
    | exact resolve eq112578 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq112578
  have eq112600 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105937 eq112588
    | exact resolve eq112588 eq105937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105937 eq112588
  have eq112611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112161 eq112600
    | exact resolve eq112600 eq112161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112161 eq112600
  have eq112620 : False := by grind
  exact eq112620

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq163 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq167 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq163 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq163 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq163 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq163 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq163 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq1335 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq167
  have eq1356 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1335 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1668 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1356 (σ X1) (σ X0)
       grind)
    | exact superpose eq1356 eq15
    | exact resolve eq15 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1679 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1668 X0 X1
       have i₂ := eq1356 X1 X0
       grind)
    | exact superpose eq1356 eq1668
    | exact resolve eq1668 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356 eq1668
  have eq1689 : False := by grind
  exact eq1689

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pxy_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq56 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq668 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq671 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq57 eq58
    | exact resolve eq58 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq58
  have eq10464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq10465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq10464
    | exact resolve eq10464 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10464
  have eq10476 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq10465
       have r₂ := eq28
       grind)
    | exact resolve eq10465 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10465
  have eq10480 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq10476
    | exact resolve eq10476 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10476
  have eq10522 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10480 eq668
    | exact resolve eq668 eq10480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10480
  have eq10532 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq671 eq10522
    | exact resolve eq10522 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq10522
  have eq10533 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10532
  have eq10572 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq668 x X0 x
       have i₂ := eq10533
       grind)
    | exact superpose eq10533 eq668
    | exact resolve eq668 eq10533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq10533
  have eq10582 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq670 eq10572
    | exact resolve eq10572 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq10572
  have eq10583 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq10582
  have eq10604 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq10583 eq30
    | exact resolve eq30 eq10583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10583
  have eq10711 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq10604
    | exact resolve eq10604 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10604
  have eq10712 : x = y := by grind
  clear eq10711
  have eq10731 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq10712
       grind)
    | exact superpose eq10712 eq19
    | exact resolve eq19 eq10712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq10732 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq10712
       grind)
    | exact superpose eq10712 eq25
    | exact resolve eq25 eq10712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq10712
  have eq10841 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10732
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10732
    | exact resolve eq10732 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10732
  have eq10856 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10841 eq27
    | exact resolve eq27 eq10841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10841
  have eq11311 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq10856 eq70
    | exact resolve eq70 eq10856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq10856
  have eq11371 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11311
       have i₂ := eq10731
       grind)
    | exact superpose eq10731 eq11311
    | exact resolve eq11311 eq10731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10731 eq11311
  have eq11380 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11371 eq15
    | exact resolve eq15 eq11371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11371
  have eq11424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11380
    | exact resolve eq11380 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq11380
  have eq11433 : False := by grind
  exact eq11433
