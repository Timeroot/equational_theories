import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_pyx_pxy_Equation3071 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
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
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) X3) (M.op (M.op (M.op X0 X1) X0) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op (M.op X0 X1) X0) X2) X0 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X1) X0 X0
       have i₂ := eq16 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq40
    | exact resolve eq40 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq41
    | exact resolve eq41 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq181
    | exact resolve eq181 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq183 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq180
    | exact resolve eq180 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq191 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq141
    | exact resolve eq141 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq240
    | exact resolve eq240 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq268 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq152
    | exact resolve eq152 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq289 : y = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq31 eq268
    | exact resolve eq268 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq740 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq178
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (k X0 X1) X0) X2) X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq11 X0 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq178
    | (have j1 := eq11 X0 (M.op X0 X1)
       grind)
    | exact resolve eq178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 ∨ (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) = X0 ∨ (M.op (M.op (M.op X0 X1) X0) X2) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 (M.op (M.op (M.op X0 X1) X0) X2) X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (M.op (M.op X0 X1) X0) X2) X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X2 ∨ (M.op (k (M.op (M.op X0 X1) X0) X2) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 (M.op (M.op X0 X1) X0) X2
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (M.op X0 X1) X0) X2
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq757 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq191
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq191
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq763 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq194
       have i₂ := eq11 sF2 sF4
       grind)
    | exact superpose eq11 eq194
    | (have j1 := eq11 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq786 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq763
       have r₂ := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq763
       have r₂ := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq763 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq790 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq757
       have r₂ := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq757
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq757 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq799 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) = X0 ∨ (k (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq744 X0 X1 X2
       have j1 := eq13 (M.op (M.op (M.op X0 X1) X0) X2) X0
       grind)
    | (have r₁ := eq744 (M.op X1 X1) X1 X2
       have r₂ := eq13 (k (M.op (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1)) X2) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq744 X0 X1 X2
       have r₂ := eq13 X0 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | (have r₁ := eq744 (M.op X1 X1) X1 X2
       have r₂ := eq13 (M.op (M.op (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1)) X2) (M.op (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1)) X2)) X1
       grind)
    | exact resolve eq744 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq800 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq742 X0 X1
       have j1 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq742 X1 X1
       have r₂ := eq13 (k X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq742 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq742 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq742 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq822 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq769 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq769
    | (have j0 := eq769 (σ X0)
       grind)
    | exact resolve eq769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq786 eq90
    | exact resolve eq90 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1498 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq755
       grind)
    | exact superpose eq755 eq40
    | exact resolve eq40 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1499 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1498
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1498
    | exact resolve eq1498 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1501 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1499
    | exact resolve eq1499 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq3691 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq822 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq822
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq822 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3695 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3691
  have eq7821 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op (M.op (M.op x y) x) X0)) X1) = (M.op (M.op (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x (M.op (M.op (M.op x y) x) X0)) X1)) X2) (M.op (M.op x (M.op (M.op (M.op x y) x) X0)) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq12074 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq799 (k X0 X1) X0 X0
       have i₂ := eq741 X0 X1 (k X0 X1)
       grind)
    | exact superpose eq741 eq799
    | (have j1 := eq741 X0 X1 x
       grind)
    | exact resolve eq799 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq12081 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) = X0 ∨ (k (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 ∨ (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) ∨ (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq799 X0 X1 X2
       have i₂ := eq11 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq11 eq799
    | (have j0 := eq799 X0 X1 X2
       have j1 := eq11 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact resolve eq799 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12085 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) = (k (M.op (M.op (M.op X0 X1) X0) X2) X0) ∨ (M.op (M.op (M.op X0 X1) X0) X2) = (M.op X0 X0) ∨ (k (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq822 (M.op (M.op (M.op X0 X1) X0) X2)
       have i₂ := eq799 X0 X1 X2
       grind)
    | exact superpose eq799 eq822
    | (have j1 := eq799 X0 X1 X2
       grind)
    | exact resolve eq822 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12090 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) = X0 ∨ (M.op (M.op (M.op X0 X1) X0) X2) = X0 ∨ (M.op (M.op (M.op X0 X1) X0) X2) = X0 ∨ (k (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)
       have i₂ := eq799 X0 X1 X2
       grind)
    | exact superpose eq799 eq11
    | (have j1 := eq799 X0 X1 X2
       grind)
    | exact resolve eq11 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq12093 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) = X0 ∨ (M.op (M.op (M.op X0 X1) X0) X2) = X0 ∨ (k (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq12090 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12090
  have eq12094 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) = X0 ∨ (k (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 ∨ (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq12081 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12081
  have eq12095 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) = (k (M.op (M.op (M.op X0 X1) X0) X2) X0) ∨ (k (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq12085 X0 X1 X2
       have j1 := eq13 (M.op (M.op (M.op X0 X1) X0) X2) X0
       grind)
    | (have r₁ := eq12085 X0 X1 (M.op (M.op X0 X1) X0)
       have r₂ := eq13 (M.op X0 X0) (M.op (M.op X0 X1) X0)
       grind)
    | (have r₁ := eq12085 X1 X1 X2
       have r₂ := eq13 (M.op (M.op (M.op X1 X1) X1) X2) X1
       grind)
    | (have r₁ := eq12085 (M.op X1 X1) X1 X2
       have r₂ := eq13 (k (M.op (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1)) X2) (M.op X1 X1)) X1
       grind)
    | exact resolve eq12085 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12085
  have eq12096 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) = X0 ∨ (k (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq12093 eq12094
    | (have j0 := eq12094 X0 X1 X2
       have j1 := eq12093 X0 X1 X2
       grind)
    | exact resolve eq12094 eq12093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12094
  have eq14234 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq747 X0 X1 (M.op (M.op X0 X1) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq14235 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) ∨ (M.op (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14234 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14234
  have eq16700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1501 eq762
    | exact resolve eq762 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16708 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16700
       have r₂ := eq27
       grind)
    | exact resolve eq16700 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16700
  have eq16715 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16708 eq261
    | exact resolve eq261 eq16708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16723 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16708 eq178
    | exact resolve eq178 eq16708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16708
  have eq16729 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq16723
    | exact resolve eq16723 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16723
  have eq16731 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq16715
    | exact resolve eq16715 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16715
  have eq16732 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16731
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq16731
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq16731
       have r₂ := eq13 x y
       grind)
    | exact resolve eq16731 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16731
  have eq16734 : y = (k (τ (σ x)) y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16732 eq289
    | exact resolve eq289 eq16732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16732
  have eq16752 : y = (k x y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq16734
    | exact resolve eq16734 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16734
  have eq16756 : y = (k x y) ∨ x = (k y x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq16752
       have r₂ := eq13 x y
       grind)
    | exact resolve eq16752 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16752
  have eq16761 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq755
       have i₂ := eq16756
       grind)
    | exact superpose eq16756 eq755
    | exact resolve eq755 eq16756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16756
  have eq16768 : x = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16761
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq16761
       have r₂ := eq13 x y
       grind)
    | exact resolve eq16761 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16761
  have eq16943 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq740 y x
       have i₂ := eq16768
       grind)
    | exact superpose eq16768 eq740
    | (have j0 := eq740 y x
       grind)
    | exact resolve eq740 eq16768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16768
  have eq16969 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq16943
  have eq17058 : y = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16729 eq289
    | exact resolve eq289 eq16729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq16729
  have eq17076 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq17058
    | exact resolve eq17058 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17058
  have eq17080 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq17076
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq17076
       have r₂ := eq13 x y
       grind)
    | exact resolve eq17076 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17076
  have eq17085 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq755
       have i₂ := eq17080
       grind)
    | exact superpose eq17080 eq755
    | exact resolve eq755 eq17080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17086 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq17080
       grind)
    | exact superpose eq17080 eq35
    | exact resolve eq35 eq17080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17080
  have eq17092 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17085
  have eq17097 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17086
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17086
    | exact resolve eq17086 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17086
  have eq17107 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17097 eq762
    | exact resolve eq762 eq17097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17097
  have eq17114 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq17107
  have eq17135 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq17092
       grind)
    | exact superpose eq17092 eq178
    | exact resolve eq178 eq17092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17092
  have eq17141 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17135
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17135
    | exact resolve eq17135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17135
  have eq17142 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17141
  have eq17145 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq183
       have i₂ := eq17142
       grind)
    | exact superpose eq17142 eq183
    | exact resolve eq183 eq17142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq17146 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq822 y
       have i₂ := eq17142
       grind)
    | exact superpose eq17142 eq822
    | exact resolve eq822 eq17142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17142
  have eq17162 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17146
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17146
    | exact resolve eq17146 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17146
  have eq17163 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17145
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17145
    | exact resolve eq17145 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17145
  have eq17206 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17163 eq762
    | exact resolve eq762 eq17163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq17163
  have eq17212 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17206
  have eq17325 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq17162
       grind)
    | exact superpose eq17162 eq39
    | exact resolve eq39 eq17162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17162
  have eq17332 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17325
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17325
    | exact resolve eq17325 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17325
  have eq17336 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17332
    | exact resolve eq17332 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17332
  have eq17372 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17212 eq178
    | exact resolve eq178 eq17212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17212
  have eq17378 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17372
    | exact resolve eq17372 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17372
  have eq17379 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17378
  have eq17384 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17379 eq822
    | exact resolve eq822 eq17379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17379
  have eq17400 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17384
    | exact resolve eq17384 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17384
  have eq17584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17400 eq17336
    | exact resolve eq17336 eq17400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17336 eq17400
  have eq17593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq17584
  have eq17600 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17593
       have r₂ := eq27
       grind)
    | exact resolve eq17593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17593
  have eq17627 : x = (k (τ (σ y)) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17600 eq261
    | exact resolve eq261 eq17600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17635 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17600 eq178
    | exact resolve eq178 eq17600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17600
  have eq17642 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq17635
    | exact resolve eq17635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17635
  have eq17643 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17642
  have eq17646 : x = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17627
    | exact resolve eq17627 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17627
  have eq17649 : x = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq17646
       have r₂ := eq13 y x
       grind)
    | exact resolve eq17646 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17646
  have eq17659 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq17643
       grind)
    | exact superpose eq17643 eq178
    | exact resolve eq178 eq17643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17643
  have eq17666 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17659
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17659
    | exact resolve eq17659 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17659
  have eq17667 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17666
  have eq17673 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17667 eq27
    | exact resolve eq27 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17674 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ y) (σ x)) X0) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17667 eq176
    | exact resolve eq176 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq17678 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17667 eq826
    | exact resolve eq826 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq17680 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq17678
    | exact resolve eq17678 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17678
  have eq17743 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17680 eq11
    | exact resolve eq11 eq17680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17749 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq17743
  have eq17853 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17749 eq97
    | exact resolve eq97 eq17749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq17749
  have eq17868 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq17853
    | exact resolve eq17853 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17853
  have eq17876 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq755
       have i₂ := eq17868
       grind)
    | exact superpose eq17868 eq755
    | exact resolve eq755 eq17868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17868
  have eq17881 : y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq17876
  have eq18010 : x = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17114 eq261
    | exact resolve eq261 eq17114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18019 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17114 eq178
    | exact resolve eq178 eq17114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17114
  have eq18029 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq18019
    | exact resolve eq18019 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18019
  have eq18030 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq18029
  have eq18038 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq18010
    | exact resolve eq18010 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18010
  have eq18040 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq17667 eq18030
    | exact resolve eq18030 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18030
  have eq18041 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq18038
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq18038
       have r₂ := eq13 y x
       grind)
    | exact resolve eq18038 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18038
  have eq18042 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq17667 eq18041
    | exact resolve eq18041 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18041
  have eq18043 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq18040
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq18040
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq18040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18045 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18040 eq822
    | exact resolve eq822 eq18040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18049 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18040 eq11
    | (have j0 := eq11 x (M.op x y)
       grind)
    | exact resolve eq11 eq18040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18040
  have eq18055 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq18049
  have eq18056 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq18043
  have eq18061 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq18045
    | exact resolve eq18045 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18045
  have eq18063 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18055 eq18056
    | exact resolve eq18056 eq18055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18055 eq18056
  have eq18142 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq18042 eq822
    | exact resolve eq822 eq18042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18147 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq18042 eq16
    | exact resolve eq16 eq18042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18042
  have eq18157 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq26 eq18147
    | (have j0 := eq18147 X0
       grind)
    | exact resolve eq18147 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18147
  have eq18158 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq18142
    | exact resolve eq18142 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18142
  have eq18559 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq16969
       grind)
    | exact superpose eq16969 eq178
    | exact resolve eq178 eq16969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16969
  have eq18568 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18559
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18559
    | exact resolve eq18559 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18559
  have eq18569 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq18568
  have eq18581 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq178 y y
       have i₂ := eq18569
       grind)
    | exact superpose eq18569 eq178
    | exact resolve eq178 eq18569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18584 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq18581
  have eq18593 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18584
       grind)
    | exact superpose eq18584 eq16
    | exact resolve eq16 eq18584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18606 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18593 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18593
    | (have j0 := eq18593 X0
       grind)
    | exact resolve eq18593 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18593
  have eq18618 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) = (M.op y (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f18618_13 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) X3) (M.op (M.op (M.op X0 X1) X0) X2)) := by
      intro X0 X1 X2 X3
      grind
    have f18618_14 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f18618_23 : (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) ≠ (M.op y (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1)) := by grind
    have f18618_24 : y ≠ (M.op x y) := by grind
    have f18618_27 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) := by
      intro X0
      first
      | (have j0 := f18618_14 X0
         grind)
      | (have r₁ := f18618_14 X0
         have r₂ := f18618_24
         grind)
      | exact resolve f18618_14 f18618_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f18618_86 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) = (M.op y (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1)) := by
      intro X0 X1
      first
      | (have i₁ := f18618_13 (M.op x y) X0 X1 y
         have i₂ := f18618_27 (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1)
         grind)
      | exact superpose f18618_27 f18618_13
      | exact resolve f18618_13 f18618_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f18618_1141 : (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) ≠ (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) := by
      first
      | (have i₁ := f18618_23
         have i₂ := f18618_86 X0 X1
         grind)
      | exact superpose f18618_86 f18618_23
      | (have r₁ := f18618_23
         have r₂ := f18618_86 X0 X1
         grind)
      | exact resolve f18618_23 f18618_86
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f18618_1147 : False := by grind
    exact f18618_1147
  clear eq177
  have eq19003 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18061 eq114
    | exact resolve eq114 eq18061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18061
  have eq19032 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq17667 eq19003
    | exact resolve eq19003 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19003
  have eq19036 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18063 eq115
    | exact resolve eq115 eq18063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq18063
  have eq19058 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29 eq19036
    | exact resolve eq19036 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19036
  have eq19063 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq17667 eq19058
    | exact resolve eq19058 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19058
  have eq19073 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq18158 eq114
    | exact resolve eq114 eq18158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq18158
  have eq19102 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq17667 eq19073
    | exact resolve eq19073 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19073
  have eq19156 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19063 eq16
    | exact resolve eq16 eq19063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19173 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19063 eq19156
    | exact resolve eq19156 eq19063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19063 eq19156
  have eq20033 : (k (σ (M.op x y)) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq19032 eq39
    | exact resolve eq39 eq19032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19032
  have eq20041 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20033
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq20033
    | exact resolve eq20033 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20033
  have eq20048 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq20041
    | exact resolve eq20041 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20041
  have eq20079 : (k (σ (M.op x y)) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq19102 eq39
    | exact resolve eq39 eq19102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20082 : x ≠ (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq19102
  have eq20084 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq20079
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq20079
    | exact resolve eq20079 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20079
  have eq20090 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq20 eq20084
    | exact resolve eq20084 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20084
  have eq21078 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) y) X2) y) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f21078_14 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) = (M.op y (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1)) ∨ y = (M.op x y) := by
      intro X0 X1
      grind
    have f21078_22 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f21078_23 : y ≠ (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) y) X2) y) := by grind
    have f21078_24 : y ≠ (M.op x y) := by grind
    have f21078_27 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) = (M.op y (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1)) := by
      intro X0 X1
      first
      | (have j0 := f21078_14 X0 X1
         grind)
      | (have r₁ := f21078_14 X0 X1
         have r₂ := f21078_24
         grind)
      | exact resolve f21078_14 f21078_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f21078_110 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) y) X2) y) := by
      intro X0 X1 X2
      first
      | (have i₁ := f21078_22 y (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X1) X2
         have i₂ := f21078_27 X0 X1
         grind)
      | exact superpose f21078_27 f21078_22
      | exact resolve f21078_22 f21078_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f21078_418 : y ≠ y := by
      first
      | (have i₁ := f21078_23
         have i₂ := f21078_110 X0 X1 X2
         grind)
      | exact superpose f21078_110 f21078_23
      | (have r₁ := f21078_23
         have r₂ := f21078_110 X0 X1 X2
         grind)
      | exact resolve f21078_23 f21078_110
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f21078_422 : False := by grind
    exact f21078_422
  clear eq18618
  have eq21556 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq194 eq19173
    | (have j0 := eq19173 (σ y)
       grind)
    | exact resolve eq19173 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19173
  have eq21619 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21556 eq18157
    | exact resolve eq18157 eq21556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21556
  have eq21633 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq21619
  have eq21645 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq21633
       have r₂ := eq13 (M.op x y) x
       grind)
    | exact resolve eq21633 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21633
  have eq21656 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq21645
    | exact resolve eq21645 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21645
  have eq21657 : x = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21656
  have eq21704 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21657 eq41
    | exact resolve eq41 eq21657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq21711 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21657 eq3695
    | (have j0 := eq3695 (M.op x y)
       grind)
    | exact resolve eq3695 eq21657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21657
  have eq21718 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq21711
       have r₂ := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq21711
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq21711 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21711
  have eq21721 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq21704
    | exact resolve eq21704 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21704
  have eq21725 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq191 eq21718
    | exact resolve eq21718 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq21718
  have eq21728 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21721
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21721
    | exact resolve eq21721 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21721
  have eq22058 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21725 eq39
    | exact resolve eq39 eq21725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21725
  have eq22072 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22058
    | exact resolve eq22058 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22058
  have eq22256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22072 eq20090
    | exact resolve eq20090 eq22072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20090 eq22072
  have eq22269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq22256
  have eq22285 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq22269
       have r₂ := eq27
       grind)
    | exact resolve eq22269 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22269
  have eq22592 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq22285 eq178
    | exact resolve eq178 eq22285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22285
  have eq22606 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq22592
    | exact resolve eq22592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22592
  have eq22607 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22606
  have eq22614 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22607 eq182
    | exact resolve eq182 eq22607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq22629 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22607 eq174
    | exact resolve eq174 eq22607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22607
  have eq22643 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22614
    | exact resolve eq22614 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22614
  have eq22648 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21728 eq22643
    | exact resolve eq22643 eq21728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21728 eq22643
  have eq22723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22629 eq824
    | (have j0 := eq824 (M.op x y)
       grind)
    | exact resolve eq824 eq22629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22629
  have eq22731 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22723
  have eq22741 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22731
    | exact resolve eq22731 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22731
  have eq22748 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22648 eq22741
    | exact resolve eq22741 eq22648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22648 eq22741
  have eq22830 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) X0) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22748 eq16
    | exact resolve eq16 eq22748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22850 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22748 eq22830
    | exact resolve eq22830 eq22748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22748 eq22830
  have eq23005 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq194 eq22850
    | (have j0 := eq22850 (σ y)
       grind)
    | exact resolve eq22850 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22850
  have eq23062 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23005 eq18157
    | exact resolve eq18157 eq23005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18157
  have eq23076 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq23062
  have eq23087 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq23076
    | exact resolve eq23076 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23076
  have eq23088 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23087
  have eq23112 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23088 eq37
    | exact resolve eq37 eq23088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23088
  have eq23122 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23112
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23112
    | exact resolve eq23112 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23112
  have eq23133 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23122 eq20048
    | exact resolve eq20048 eq23122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20048 eq23122
  have eq23142 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq23133
  have eq23225 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq23142 eq178
    | exact resolve eq178 eq23142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23142
  have eq23242 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq23225
    | exact resolve eq23225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23225
  have eq23243 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23242
  have eq23267 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq23243
       grind)
    | exact superpose eq23243 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq23243
       grind)
    | exact resolve eq13 eq23243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23268 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq23243
       grind)
    | exact superpose eq23243 eq11
    | exact resolve eq11 eq23243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23243
  have eq23274 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23268
  have eq23301 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq23274
       grind)
    | exact superpose eq23274 eq39
    | exact resolve eq39 eq23274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23321 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23301
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23301
    | exact resolve eq23301 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23301
  have eq23327 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23321
    | exact resolve eq23321 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23321
  have eq23362 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23327 eq740
    | (have j0 := eq740 (σ x) (σ x)
       grind)
    | exact resolve eq740 eq23327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23327
  have eq23365 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23362
  have eq24802 : x = (k (τ (σ x)) x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23365 eq261
    | exact resolve eq261 eq23365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23365
  have eq24859 : x = (k x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq24802
    | exact resolve eq24802 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24802
  have eq24868 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq23267 x
       grind)
    | (have r₁ := eq24859
       have r₂ := eq23267 x
       grind)
    | exact resolve eq24859 eq23267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24859
  have eq32115 : (k x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3695 x
       have i₂ := eq17881
       grind)
    | exact superpose eq17881 eq3695
    | (have j0 := eq3695 x
       grind)
    | exact resolve eq3695 eq17881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32119 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq740 x x
       have i₂ := eq17881
       grind)
    | exact superpose eq17881 eq740
    | (have j0 := eq740 x x
       grind)
    | exact resolve eq740 eq17881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32122 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq32119
  have eq32125 : (k x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq32115
  have eq32153 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32122
    | exact resolve eq32122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32122
  have eq32154 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq32153
  have eq32158 : (k x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq32125
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq32125
       have r₂ := eq12 x x
       grind)
    | (have r₁ := eq32125
       have r₂ := eq12 x y
       grind)
    | exact resolve eq32125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32125
  have eq32180 : x = (k x y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18569 eq32158
    | exact resolve eq32158 eq18569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18569 eq32158
  have eq32303 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32154
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq32154
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq32154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32329 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq32154
       grind)
    | exact superpose eq32154 eq178
    | exact resolve eq178 eq32154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32154
  have eq32358 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq32303
  have eq32380 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32329
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32329
    | exact resolve eq32329 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32329
  have eq32381 : x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq32380
  have eq32395 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq32358
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq32358
       have r₂ := eq13 x x
       grind)
    | exact resolve eq32358 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32358
  have eq32669 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12074 x y
       have i₂ := eq32180
       grind)
    | exact superpose eq32180 eq12074
    | (have j0 := eq12074 x x
       grind)
    | exact resolve eq12074 eq32180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12074 eq32180
  have eq32674 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq32669
  have eq32687 : x = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq32674
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq32674
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq32674
       have r₂ := eq13 x y
       grind)
    | exact resolve eq32674 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32674
  have eq32689 : x = (k x x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32381 eq32687
    | exact resolve eq32687 eq32381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32687
  have eq32718 : x = y ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17881
       have i₂ := eq32689
       grind)
    | exact superpose eq32689 eq17881
    | exact resolve eq17881 eq32689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17881
  have eq32757 : x = y ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq32718
  have eq32787 : x = y ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32381 eq32757
    | exact resolve eq32757 eq32381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32381 eq32757
  have eq32788 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq32787
  have eq32805 : x = (k y y) ∨ x = y ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq32788
       grind)
    | exact superpose eq32788 eq11
    | exact resolve eq11 eq32788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32788
  have eq32817 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq32805
  have eq33236 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq32817
       grind)
    | exact superpose eq32817 eq40
    | exact resolve eq40 eq32817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32817
  have eq33259 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33236
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33236
    | exact resolve eq33236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33236
  have eq33267 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33259
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33259
    | exact resolve eq33259 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33259
  have eq33317 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33267 eq740
    | (have j0 := eq740 (σ y) (σ y)
       grind)
    | exact resolve eq740 eq33267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33320 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq33317
  have eq33650 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33320 eq174
    | exact resolve eq174 eq33320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq33320
  have eq33693 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33267 eq33650
    | exact resolve eq33650 eq33267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33267 eq33650
  have eq33694 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq33693
  have eq33728 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq33694 eq800
    | exact resolve eq800 eq33694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800 eq33694
  have eq34042 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq33728 eq107
    | exact resolve eq107 eq33728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq33728
  have eq34061 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq34042
    | exact resolve eq34042 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34042
  have eq34081 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq34061 eq822
    | exact resolve eq822 eq34061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34061
  have eq34116 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq34081
    | exact resolve eq34081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34081
  have eq34131 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq17649 eq34116
    | exact resolve eq34116 eq17649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34116
  have eq34579 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq32395
  have eq34612 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq34579
       have r₂ := eq32689
       grind)
    | exact resolve eq34579 eq32689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32689 eq34579
  have eq34683 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq824 x
       have i₂ := eq34612
       grind)
    | exact superpose eq34612 eq824
    | (have j0 := eq824 x
       grind)
    | exact resolve eq824 eq34612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34612
  have eq34696 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq34683
  have eq34732 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34696
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34696
    | exact resolve eq34696 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34696
  have eq34770 : (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq34732 eq17680
    | exact resolve eq17680 eq34732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17680 eq34732
  have eq34814 : (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq34770
  have eq34847 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq34814
       have r₂ := eq13 x y
       grind)
    | exact resolve eq34814 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34814
  have eq34879 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq34847
       grind)
    | exact superpose eq34847 eq35
    | exact resolve eq35 eq34847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq34847
  have eq34895 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34879
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34879
    | exact resolve eq34879 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34879
  have eq35940 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17674 eq12096
    | (have j0 := eq12096 (σ y) x x
       grind)
    | exact resolve eq12096 eq17674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12096 eq17674
  have eq35979 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34895 eq35940
    | exact resolve eq35940 eq34895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35940
  have eq36045 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34895 eq35979
    | exact resolve eq35979 eq34895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34895 eq35979
  have eq36102 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq36045
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq36045 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36045
  have eq36173 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36102 eq90
    | exact resolve eq90 eq36102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq36102
  have eq36183 : (σ x) = (k (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq36173
    | exact resolve eq36173 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36173
  have eq36237 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36183 eq141
    | exact resolve eq141 eq36183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq36183
  have eq36280 : y = (k x y) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq36237
    | exact resolve eq36237 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36237
  have eq36411 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq755
       have i₂ := eq36280
       grind)
    | exact superpose eq36280 eq755
    | exact resolve eq755 eq36280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq36280
  have eq36421 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) := by grind
  clear eq36411
  have eq36905 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq36421
       grind)
    | exact superpose eq36421 eq178
    | exact resolve eq178 eq36421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36916 : (M.op y x) = (M.op (M.op y x) (M.op y x)) ∨ x = (M.op (k (M.op y x) (M.op y x)) x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14235 x x
       have i₂ := eq36421
       grind)
    | exact superpose eq36421 eq14235
    | exact resolve eq14235 eq36421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14235 eq36421
  have eq36950 : x = (M.op x x) ∨ x = (M.op (k (M.op y x) (M.op y x)) x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | exact superpose eq18584 eq36916
    | exact resolve eq36916 eq18584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36916
  have eq36961 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq36905
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36905
    | exact resolve eq36905 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36905
  have eq36962 : x = (k x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq36961
  have eq36981 : x = (M.op x x) ∨ x = (M.op (k (M.op y x) (M.op y x)) x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq769 x
       grind)
    | (have r₁ := eq36950
       have r₂ := eq769 x
       grind)
    | exact resolve eq36950 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36950
  have eq36992 : x = (M.op x x) ∨ x = (M.op (k x x) x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18584 eq36981
    | exact resolve eq36981 eq18584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18584 eq36981
  have eq36993 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq36962 eq36992
    | exact resolve eq36992 eq36962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36962 eq36992
  have eq36994 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq36993
  have eq37105 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq822 y
       have i₂ := eq36994
       grind)
    | exact superpose eq36994 eq822
    | exact resolve eq822 eq36994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq36994
  have eq37139 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37105
    | exact resolve eq37105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37105
  have eq48297 : ∀ X0 : G, y = (M.op (M.op (M.op x (M.op (M.op (M.op x y) x) (M.op x y))) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7821 eq21078
    | exact resolve eq21078 eq7821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7821 eq21078
  have eq48471 : (M.op x y) = (k y x) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48297 eq12095
    | exact resolve eq12095 eq48297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12095
  have eq48495 : (M.op x y) = (k y x) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq48471
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq48471
    | exact resolve eq48471 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48471
  have eq48510 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq48495
       grind)
    | exact superpose eq48495 eq39
    | exact resolve eq39 eq48495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq48495
  have eq48524 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq48510
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48510
    | exact resolve eq48510 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48510
  have eq48529 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq48524
    | exact resolve eq48524 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48524
  have eq51008 : x = (k y y) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48297 eq12093
    | exact resolve eq12093 eq48297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12093
  have eq51577 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq51008
       grind)
    | exact superpose eq51008 eq40
    | exact resolve eq40 eq51008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq51008
  have eq51609 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51577
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51577
    | exact resolve eq51577 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51577
  have eq51618 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51609
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51609
    | exact resolve eq51609 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51609
  have eq51645 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51618 eq3695
    | (have j0 := eq3695 (σ y)
       grind)
    | exact resolve eq3695 eq51618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3695 eq51618
  have eq51665 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq51645
    | exact resolve eq51645 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51645
  have eq51677 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17649 eq51665
    | exact resolve eq51665 eq17649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17649 eq51665
  have eq51684 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34131 eq51677
    | exact resolve eq51677 eq34131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34131 eq51677
  have eq51686 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48529 eq51684
    | exact resolve eq51684 eq48529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48529 eq51684
  have eq51687 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq51686
       have r₂ := eq17673
       grind)
    | exact resolve eq51686 eq17673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17673 eq51686
  have eq51997 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51687 eq261
    | exact resolve eq261 eq51687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51687
  have eq52097 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq51997
    | exact resolve eq51997 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51997
  have eq52098 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq52097
  have eq52131 : x = (k (τ (σ x)) x) ∨ x = (k y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq52098 eq261
    | exact resolve eq261 eq52098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52098
  have eq52221 : x = (k y x) ∨ x = (k x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq52131
    | exact resolve eq52131 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52131
  have eq52385 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (k x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37139
       have i₂ := eq52221
       grind)
    | exact superpose eq52221 eq37139
    | exact resolve eq37139 eq52221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37139 eq52221
  have eq52398 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (k x x) ∨ x = y := by grind
  clear eq52385
  have eq52413 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have j1 := eq769 x
       grind)
    | (have r₁ := eq52398
       have r₂ := eq769 x
       grind)
    | exact resolve eq52398 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq52398
  have eq53294 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq52413
       grind)
    | exact superpose eq52413 eq178
    | exact resolve eq178 eq52413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52413
  have eq53355 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq53294
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53294
    | exact resolve eq53294 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53294
  have eq53356 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq53355
  have eq53437 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 x x X0
       have i₂ := eq53356
       grind)
    | exact superpose eq53356 eq16
    | exact resolve eq16 eq53356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53508 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq53356 eq53437
    | exact resolve eq53437 eq53356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53356 eq53437
  have eq53999 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq48297 x
       have i₂ := eq53508 (M.op (M.op sF0 x) sF0)
       grind)
    | exact superpose eq53508 eq48297
    | exact resolve eq48297 eq53508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53508
  have eq54043 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq53999
  have eq54084 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq54043
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54043
    | exact resolve eq54043 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54043
  have eq54085 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq54084
  have eq55928 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq54085
       grind)
    | exact superpose eq54085 eq24
    | exact resolve eq24 eq54085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54085
  have eq55979 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq55928
    | exact resolve eq55928 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55928
  have eq56083 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq55979 eq24868
    | exact resolve eq24868 eq55979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24868
  have eq56138 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have j1 := eq23267 x
       grind)
    | (have r₁ := eq56083
       have r₂ := eq23267 x
       grind)
    | exact resolve eq56083 eq23267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56083
  have eq56241 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq56138
    | exact resolve eq56138 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56138
  have eq56242 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq56241
  have eq56256 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17667 eq56242
    | exact resolve eq56242 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17667 eq56242
  have eq56264 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq23267 x
       grind)
    | (have r₁ := eq56256
       have r₂ := eq23267 x
       grind)
    | exact resolve eq56256 eq23267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23267 eq56256
  have eq56381 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23274
       have i₂ := eq56264
       grind)
    | exact superpose eq56264 eq23274
    | exact resolve eq23274 eq56264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23274 eq56264
  have eq56415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq56381
  have eq56480 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56415 eq27
    | exact resolve eq27 eq56415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56486 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56415 eq786
    | exact resolve eq786 eq56415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq56415
  have eq56505 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq55979 eq56480
    | (have r₁ := eq56480
       have r₂ := eq55979
       grind)
    | exact resolve eq56480 eq55979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55979
  have eq56506 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq56505
  have eq56507 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq56506
  have eq56512 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56507 eq194
    | exact resolve eq194 eq56507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56874 : x = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56512 eq261
    | exact resolve eq261 eq56512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56959 : x = (k x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq56874
    | exact resolve eq56874 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56874
  have eq57235 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq740 x x
       have i₂ := eq56959
       grind)
    | exact superpose eq56959 eq740
    | (have j0 := eq740 x x
       grind)
    | exact resolve eq740 eq56959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56959
  have eq57248 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq57235
  have eq64611 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56486 eq1501
    | exact resolve eq1501 eq56486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq56486
  have eq64638 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq64611
       have r₂ := eq56480
       grind)
    | exact resolve eq64611 eq56480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64611
  have eq64645 : x = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56507 eq64638
    | exact resolve eq64638 eq56507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56507 eq64638
  have eq64647 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57248 eq64645
    | exact resolve eq64645 eq57248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64645
  have eq64648 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq64647
  have eq65284 : x = (k (τ (σ y)) x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64648 eq261
    | exact resolve eq261 eq64648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64648
  have eq65399 : x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq65284
    | exact resolve eq65284 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq65284
  have eq65422 : x = (k x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57248 eq65399
    | exact resolve eq65399 eq57248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57248 eq65399
  have eq65426 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq65422
       have r₂ := eq13 x x
       grind)
    | exact resolve eq65422 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65422
  have eq65483 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq740 x x
       have i₂ := eq65426
       grind)
    | exact superpose eq65426 eq740
    | (have j0 := eq740 x x
       grind)
    | exact resolve eq740 eq65426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65426
  have eq65500 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq65483
  have eq65623 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 x x X0
       have i₂ := eq65500
       grind)
    | exact superpose eq65500 eq16
    | exact resolve eq16 eq65500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65687 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq65500 eq65623
    | exact resolve eq65623 eq65500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65500 eq65623
  have eq66100 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48297 x
       have i₂ := eq65687 (M.op (M.op sF0 x) sF0)
       grind)
    | exact superpose eq65687 eq48297
    | exact resolve eq48297 eq65687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65687
  have eq66191 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66100
    | exact resolve eq66100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66100
  have eq66192 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq66191
  have eq66245 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66192 eq194
    | exact resolve eq194 eq66192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66267 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66192 eq23005
    | exact resolve eq23005 eq66192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23005 eq66192
  have eq66288 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56512 eq66267
    | exact resolve eq66267 eq56512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56512 eq66267
  have eq66289 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq66288
  have eq66921 : x = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66245 eq261
    | exact resolve eq261 eq66245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq66245
  have eq67028 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq66921
    | exact resolve eq66921 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66921
  have eq67293 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq740 x x
       have i₂ := eq67028
       grind)
    | exact superpose eq67028 eq740
    | (have j0 := eq740 x x
       grind)
    | exact resolve eq740 eq67028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67028
  have eq67310 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq67293
  have eq67485 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 x x X0
       have i₂ := eq67310
       grind)
    | exact superpose eq67310 eq16
    | exact resolve eq16 eq67310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67559 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq67310 eq67485
    | exact resolve eq67485 eq67310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67310 eq67485
  have eq70739 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48297 x
       have i₂ := eq67559 (M.op (M.op sF0 x) sF0)
       grind)
    | exact superpose eq67559 eq48297
    | exact resolve eq48297 eq67559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48297 eq67559
  have eq70790 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq70739
  have eq70840 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70790
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq70790
    | exact resolve eq70790 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70790
  have eq70841 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq70840
  have eq70873 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq70841
       grind)
    | exact superpose eq70841 eq24
    | exact resolve eq24 eq70841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70841
  have eq70924 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq70873
    | exact resolve eq70873 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70873
  have eq71060 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70924 eq56480
    | (have r₁ := eq56480
       have r₂ := eq70924
       grind)
    | exact resolve eq56480 eq70924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56480
  have eq71082 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq71060
  have eq71083 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq71082
  have eq71168 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq71083 eq27
    | exact resolve eq27 eq71083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71170 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq71083 eq194
    | exact resolve eq194 eq71083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq71187 : x ≠ (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq71083 eq20082
    | exact resolve eq20082 eq71083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20082
  have eq71204 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq71187
       have r₂ := eq29
       grind)
    | exact resolve eq71187 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq71187
  have eq71210 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66289 eq71204
    | exact resolve eq71204 eq66289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66289 eq71204
  have eq71211 : x = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq71210
  have eq71215 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70924 eq71168
    | exact resolve eq71168 eq70924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71168
  have eq71218 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq71215
  have eq74391 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq71211 eq37
    | exact resolve eq37 eq71211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq71211
  have eq74418 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq74391
       have r₂ := eq71218
       grind)
    | exact resolve eq74391 eq71218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74391
  have eq74433 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74418
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq74418
    | exact resolve eq74418 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74418
  have eq74441 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70924 eq74433
    | exact resolve eq74433 eq70924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70924 eq74433
  have eq74486 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74441 eq740
    | (have j0 := eq740 (σ y) (σ x)
       grind)
    | exact resolve eq740 eq74441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq74441
  have eq74508 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq71170 eq74486
    | exact resolve eq74486 eq71170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74486
  have eq74525 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq74508
       have r₂ := eq71218
       grind)
    | exact resolve eq74508 eq71218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74508
  have eq75286 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74525 eq178
    | exact resolve eq178 eq74525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq74525
  have eq75304 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq75286
  have eq75364 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq75304 eq16
    | exact resolve eq16 eq75304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75304
  have eq75410 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq75364
    | (have j0 := eq75364 X0
       grind)
    | exact resolve eq75364 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75364
  have eq75436 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq71083 eq75410
    | exact resolve eq75410 eq71083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75410
  have eq75548 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq71170 eq75436
    | exact resolve eq75436 eq71170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71170 eq75436
  have eq75595 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq75548
  have eq75641 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq75595
    | exact resolve eq75595 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75595
  have eq75678 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq71083 eq75641
    | exact resolve eq75641 eq71083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71083 eq75641
  have eq75698 : x = (M.op x y) := by
    first
    | (have r₁ := eq75678
       have r₂ := eq71218
       grind)
    | exact resolve eq75678 eq71218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71218 eq75678
  have eq75707 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq75698
       grind)
    | exact superpose eq75698 eq18
    | exact resolve eq18 eq75698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq75708 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq75698
       grind)
    | exact superpose eq75698 eq22
    | exact resolve eq22 eq75698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq75737 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq790
       have i₂ := eq75698
       grind)
    | exact superpose eq75698 eq790
    | exact resolve eq790 eq75698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq75698
  have eq75959 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq75737
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq75737 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75737
  have eq75975 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq75708 eq20
    | exact resolve eq20 eq75708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76695 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75707 eq18606
    | exact resolve eq18606 eq75707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18606
  have eq76759 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75707 eq76695
    | exact resolve eq76695 eq75707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75707 eq76695
  have eq76760 : y = (M.op x y) := by grind
  clear eq76759
  have eq77438 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq76760
       grind)
    | exact superpose eq76760 eq24
    | exact resolve eq24 eq76760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq76760
  have eq77492 : (σ x) = (σ y) := by
    first
    | exact superpose eq75708 eq77438
    | exact resolve eq77438 eq75708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75708 eq77438
  have eq77505 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq77492 eq26
    | exact resolve eq26 eq77492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq77492
  have eq78145 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq75959 eq824
    | (have j0 := eq824 (M.op x y)
       grind)
    | exact resolve eq824 eq75959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq75959
  have eq78168 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq78145
  have eq78182 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq78168
    | exact resolve eq78168 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq78168
  have eq78190 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq75975 eq78182
    | exact resolve eq78182 eq75975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78182
  have eq78497 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77505 eq78190
    | exact resolve eq78190 eq77505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77505 eq78190
  have eq78604 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq78497 eq27
    | exact resolve eq27 eq78497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq78497
  have eq78647 : False := by grind
  exact eq78647

/-- `Equation3071`: `x = (((x ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation3071 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3071 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3071.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq35 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq85 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq132 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq142 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq132 X0 X1 X2
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq132
    | (have j0 := eq132 X0 X1 X2
       grind)
    | exact resolve eq132 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq132
  have eq1039 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op (M.op (M.op (τ X0) X1) (τ X0)) X2)) X0) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (M.op (M.op (τ X0) X1) (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85 (M.op (M.op (M.op (τ X1) X1) (τ X1)) X2) X1
       have i₂ := eq9 (τ X1) X1 X2
       grind)
    | exact superpose eq9 eq85
    | (have j0 := eq85 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq85 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1084 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (M.op (τ X0) X1) (τ X0)) X2) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ (M.op (M.op (M.op (τ X0) X1) (τ X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1039 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1039
    | (have j0 := eq1039 X0 X1 X2
       grind)
    | exact resolve eq1039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq3723 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (k X3 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (k (σ X0) X1)
       have i₂ := eq142 X0 X1 X2
       grind)
    | exact superpose eq142 eq13
    | (have j0 := eq13 (M.op (σ X0) (k (σ X1) X2)) (k X3 (k (σ X1) X2))
       have j1 := eq142 X1 X2 X0
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq142 X0 X1 X2
       grind)
    | exact resolve eq13 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq81209 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ (M.op (M.op (M.op (τ X0) X1) (τ X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2
       have i₂ := eq1084 X0 X1 X2
       grind)
    | exact superpose eq1084 eq9
    | (have j1 := eq1084 X0 X1 X2
       grind)
    | exact resolve eq9 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq81379 : ∀ X0 X1 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ (M.op (M.op (M.op (τ X0) X1) (τ X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81209 X0 X1 X2
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq81209
    | (have j0 := eq81209 X0 X1 X2
       grind)
    | exact resolve eq81209 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq81209
  have eq81380 : ∀ X0 X1 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ (M.op (M.op (M.op (τ X0) X1) (τ X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq81379 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81379
  have eq81482 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k (σ (M.op (M.op (M.op (τ X0) X1) (τ X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq81380 X0 X1 X2
       grind)
    | exact superpose eq81380 eq11
    | (have j1 := eq81380 X0 X1 X2
       grind)
    | exact resolve eq11 eq81380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81380
  have eq81753 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k (σ (M.op (M.op (M.op (τ X0) X1) (τ X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81482 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81482
    | (have j0 := eq81482 X0 X1 X2
       grind)
    | exact resolve eq81482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81482
  have eq82363 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ X0) = (k (σ (M.op (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) X2)) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0
       have i₂ := eq81753 (τ X0) X1 X2
       grind)
    | exact superpose eq81753 eq30
    | (have j1 := eq81753 (τ X0) X1 X2
       grind)
    | exact resolve eq30 eq81753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81753
  have eq82435 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (k (σ (M.op (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) X2)) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82363 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82363
    | (have j0 := eq82363 X0 X1 X2
       grind)
    | exact resolve eq82363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82363
  have eq86841 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ (τ X0)) = (k (σ (M.op (M.op (M.op (τ (τ (τ X0))) X1) (τ (τ (τ X0)))) X2)) (τ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0
       have i₂ := eq82435 (τ X0) X1 X2
       grind)
    | exact superpose eq82435 eq30
    | (have j1 := eq82435 (τ X0) X1 X2
       grind)
    | exact resolve eq30 eq82435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq82435
  have eq86914 : ∀ X0 X1 X2 : G, (τ (τ X0)) = (k (σ (M.op (M.op (M.op (τ (τ (τ X0))) X1) (τ (τ (τ X0)))) X2)) (τ (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86841 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86841
    | (have j0 := eq86841 X0 X1 X2
       grind)
    | exact resolve eq86841 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86841
  have eq302684 : ∀ X0 X1 X2 : G, (σ (τ (τ X0))) = (k (σ (σ (M.op (M.op (M.op (τ (τ (τ X0))) X1) (τ (τ (τ X0)))) X2))) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (τ X0) (σ (M.op (M.op (M.op (τ (τ (τ X0))) X1) (τ (τ (τ X0)))) X2))
       have i₂ := eq86914 X0 X1 X2
       grind)
    | exact superpose eq86914 eq19
    | (have j1 := eq86914 X0 X1 X2
       grind)
    | exact resolve eq19 eq86914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86914
  have eq303010 : ∀ X0 X1 X2 : G, (τ X0) = (k (σ (σ (M.op (M.op (M.op (τ (τ (τ X0))) X1) (τ (τ (τ X0)))) X2))) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302684 X0 X1 X2
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq302684
    | (have j0 := eq302684 X0 X1 X2
       grind)
    | exact resolve eq302684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302684
  have eq357304 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3723 X0 X1 X2 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723
  have eq357305 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq357304 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357304
  have eq357332 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq357305 X0 X1 X2
       have i₂ := eq35 X1 X2 X0
       grind)
    | exact superpose eq35 eq357305
    | (have j0 := eq357305 X0 X1 X2
       grind)
    | exact resolve eq357305 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq357305
  have eq357333 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq357332 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357332
  have eq358071 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 (τ X2))
       have i₂ := eq357333 (τ X0) X1 X2
       grind)
    | exact superpose eq357333 eq18
    | (have j1 := eq357333 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq357333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq357333
  have eq358481 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq358071 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq358071
    | (have j0 := eq358071 X0 X1 X2
       grind)
    | exact resolve eq358071 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358071
  have eq358674 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq358481 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq358481
    | (have j0 := eq358481 X0 X1 X2
       grind)
    | exact resolve eq358481 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358481
  have eq358823 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq358674 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq358674
    | (have j0 := eq358674 X0 X1 X2
       grind)
    | exact resolve eq358674 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358674
  have eq359107 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op X1 (k X0 X2)) ∨ (k X0 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq358823 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq358823
    | exact resolve eq358823 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359250 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq358823 X0 (σ (M.op (M.op (M.op (τ (τ (τ X0))) X1) (τ (τ (τ X0)))) x)) (τ X0)
       have i₂ := eq303010 X0 X1 x
       grind)
    | exact superpose eq303010 eq358823
    | (have j1 := eq303010 X0 X1 x
       grind)
    | exact resolve eq358823 eq303010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303010 eq358823
  have eq361277 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  clear eq359107
  have eq363930 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = X1 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0
       have i₂ := eq359250 (σ X0) X1
       grind)
    | exact superpose eq359250 eq22
    | (have j1 := eq359250 (σ X0) X1
       grind)
    | exact resolve eq22 eq359250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359250
  have eq364042 : ∀ X0 X1 : G, X0 = X1 ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq363930 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq363930
    | (have j0 := eq363930 X0 X1
       grind)
    | exact resolve eq363930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363930
  have eq364108 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq364042 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq364042
    | (have j0 := eq364042 X0 X1
       grind)
    | exact resolve eq364042 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364042
  have eq364260 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq364108 X0 X1
       grind)
    | exact superpose eq364108 eq10
    | (have j1 := eq364108 X0 X1
       grind)
    | exact resolve eq10 eq364108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364108
  have eq364677 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq364260 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq364260
    | (have j0 := eq364260 X0 X1
       grind)
    | exact resolve eq364260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364260
  have eq365834 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq361277 X0 X1
       have i₂ := eq364677 X0 X1
       grind)
    | exact superpose eq364677 eq361277
    | (have j1 := eq364677 X0 X1
       grind)
    | exact resolve eq361277 eq364677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361277 eq364677
  have eq491087 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq365834 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365834
  have eq491088 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq491087 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491087
  have eq491089 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq491088 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491088
  have eq491588 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq491089 X0 (τ X1)
       grind)
    | exact superpose eq491089 eq19
    | (have j1 := eq491089 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq491089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq491978 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq491089 (σ X0) (σ X1)
       grind)
    | exact superpose eq491089 eq15
    | (have j1 := eq491089 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq491089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491089
  have eq495941 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq491588 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq491588
    | exact resolve eq491588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491588
  have eq496553 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq495941 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq495941
    | (have j0 := eq495941 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq495941 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495941
  have eq501863 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq491978 x y
       grind)
    | exact superpose eq491978 eq16
    | (have j1 := eq491978 x y
       grind)
    | exact resolve eq16 eq491978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491978
  have eq502134 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq501863
       have i₂ := eq496553 y x
       grind)
    | exact superpose eq496553 eq501863
    | (have j1 := eq496553 (σ x) (σ y)
       grind)
    | (have r₁ := eq501863
       have r₂ := eq496553 y x
       grind)
    | (have r₁ := eq501863
       have r₂ := eq496553 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq501863
       have r₂ := eq496553 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq501863 eq496553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496553 eq501863
  have eq502137 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq502134
  have eq502787 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq502137
       grind)
    | exact superpose eq502137 eq16
    | exact resolve eq16 eq502137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502137
  have eq502788 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq502787
       have r₂ := eq22 x
       grind)
    | exact resolve eq502787 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502787
  have eq502789 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq502788
       grind)
    | exact superpose eq502788 eq16
    | exact resolve eq16 eq502788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502790 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq502788
       grind)
    | exact superpose eq502788 eq10
    | exact resolve eq10 eq502788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502788
  have eq503266 : x = y := by
    first
    | (have i₁ := eq502790
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq502790
    | exact resolve eq502790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502790
  have eq503267 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq502789
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq502789
    | exact resolve eq502789 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq502789
  have eq503272 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq503267
       have i₂ := eq503266
       grind)
    | exact superpose eq503266 eq503267
    | exact resolve eq503267 eq503266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503266 eq503267
  have eq503273 : False := by grind
  exact eq503273

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_y_pxy_Equation3081 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
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
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (k y (k X0 x)) = (τ (k (σ y) (k (σ X0) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq47 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq47
    | exact resolve eq47 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq174 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 X0) X3) (M.op (M.op (M.op X0 X1) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op (M.op X0 X1) X1) X2) X0 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) X1) X0 X2
       have i₂ := eq16 X0 X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X1) X1 X0
       have i₂ := eq16 X0 X1 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq185 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq196 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X0 X1) X2
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0) X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq178
    | exact resolve eq178 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq178
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (k X0 X1) X1) X2) X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq179
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq179 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq11 X0 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq178
    | (have j1 := eq11 X0 (M.op X0 X1)
       grind)
    | exact resolve eq178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = (M.op X0 X0) ∨ (M.op (M.op (M.op (M.op X0 X1) X1) X2) (M.op (M.op (M.op X0 X1) X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 (M.op (M.op (M.op X0 X1) X1) X2) X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (M.op (M.op X0 X1) X1) X2) X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq723 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq724 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq185
       have i₂ := eq11 sF2 sF4
       grind)
    | exact superpose eq11 eq185
    | (have j1 := eq11 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq733 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq744 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq747 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq724
       have r₂ := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq724
       have r₂ := eq12 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq724 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq752 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) (M.op (M.op (M.op X0 X1) X1) X2)) = X0 ∨ (k (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq704 X0 X1 X2
       have j1 := eq12 (M.op (M.op (M.op X0 X1) X1) X2) X0
       grind)
    | (have r₁ := eq704 (M.op X1 X1) X1 X2
       have r₂ := eq12 (k (M.op (M.op (M.op (M.op X1 X1) X1) X1) X2) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq704 X0 X1 (M.op (M.op X0 X1) X1)
       have r₂ := eq12 (M.op X0 X0) (M.op (M.op X0 X1) X1)
       grind)
    | (have r₁ := eq704 X1 X1 X2
       have r₂ := eq12 (M.op (M.op (M.op X1 X1) X1) X2) X1
       grind)
    | exact resolve eq704 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq762 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq691 X0 X1
       have j1 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq691 X1 X1
       have r₂ := eq12 (k X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq691 X0 X1
       have r₂ := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq691 (M.op X1 X1) X1
       have r₂ := eq12 (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) X1
       grind)
    | exact resolve eq691 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq779 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq734 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq734
    | (have j0 := eq734 (σ X0)
       grind)
    | exact resolve eq734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq747 eq90
    | exact resolve eq90 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq747
  have eq1633 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op (M.op x y) (M.op (M.op x X0) X0)) := by
    intro X0
    first
    | exact superpose eq181 eq177
    | (have j0 := eq177 x X0 y
       grind)
    | exact resolve eq177 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1635 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) X0)) := by
    intro X0
    first
    | exact superpose eq185 eq177
    | (have j0 := eq177 (σ x) X0 (σ y)
       grind)
    | exact resolve eq177 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1674 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq196 X0 X1 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq177 (M.op X0 X1) X2 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq196
    | exact resolve eq196 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1686 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq714
       grind)
    | exact superpose eq714 eq40
    | exact resolve eq40 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1687 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1686
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1686
    | exact resolve eq1686 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq1689 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1687
    | exact resolve eq1687 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq1820 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 (M.op (M.op X0 X1) X0) X0 X2
       have i₂ := eq1674 X0 X1 X0
       grind)
    | exact superpose eq1674 eq177
    | exact resolve eq177 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2376 : (k x (M.op x x)) = (M.op (M.op x y) (k x (M.op x x))) := by
    first
    | (have i₁ := eq1633 x
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq1633
    | exact resolve eq1633 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3017 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq665 X0
       grind)
    | exact superpose eq665 eq178
    | (have j1 := eq665 X0
       grind)
    | exact resolve eq178 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3023 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179 (M.op X0 X0)
       have i₂ := eq665 X0
       grind)
    | exact superpose eq665 eq179
    | (have j1 := eq665 X0
       grind)
    | exact resolve eq179 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3028 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3023 X0
       have i₂ := eq178 X0 X0
       grind)
    | exact superpose eq178 eq3023
    | (have j0 := eq3023 X0
       grind)
    | exact resolve eq3023 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023
  have eq3030 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3017 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq3017
    | (have j0 := eq3017 X0
       grind)
    | exact resolve eq3017 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017
  have eq16323 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1689 eq723
    | exact resolve eq723 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq16331 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16323
       have r₂ := eq27
       grind)
    | exact resolve eq16323 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16323
  have eq16354 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16331 eq178
    | exact resolve eq178 eq16331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16366 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16331 eq665
    | exact resolve eq665 eq16331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16331
  have eq16369 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq16366
  have eq16376 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq16354
    | exact resolve eq16354 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16354
  have eq16398 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16376 eq179
    | exact resolve eq179 eq16376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16409 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq16398
    | exact resolve eq16398 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16398
  have eq16465 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16369 eq107
    | exact resolve eq107 eq16369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq16369
  have eq16472 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq16465
    | exact resolve eq16465 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16465
  have eq16477 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq16472
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq16472
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq16472
       have r₂ := eq12 y x
       grind)
    | exact resolve eq16472 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16472
  have eq16481 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16477 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq16477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16491 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16477 eq1820
    | exact resolve eq1820 eq16477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16495 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16477 eq179
    | exact resolve eq179 eq16477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16501 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq16481
  have eq16503 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq16495
    | exact resolve eq16495 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16495
  have eq16504 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq26 eq16491
    | (have j0 := eq16491 X0
       grind)
    | exact resolve eq16491 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16491
  have eq16536 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16503 eq114
    | exact resolve eq114 eq16503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16642 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16501 eq115
    | exact resolve eq115 eq16501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq16501
  have eq16654 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq16642
    | exact resolve eq16642 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16642
  have eq16924 : (M.op x y) = (k y x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq744 y
       have i₂ := eq16654
       grind)
    | exact superpose eq16654 eq744
    | (have j0 := eq744 y
       grind)
    | exact resolve eq744 eq16654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16948 : (M.op x y) = (k y x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16924
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq16924
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16924 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16924
  have eq16951 : (M.op x y) = (k y x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16948
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16948
    | exact resolve eq16948 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16948
  have eq17067 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq16951
       grind)
    | exact superpose eq16951 eq39
    | exact resolve eq39 eq16951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16951
  have eq17071 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq17067
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17067
    | exact resolve eq17067 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17067
  have eq17078 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq17071
    | exact resolve eq17071 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17071
  have eq17090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq17078 eq16503
    | exact resolve eq16503 eq17078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16503 eq17078
  have eq17094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq17090
  have eq17101 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17094
       have r₂ := eq27
       grind)
    | exact resolve eq17094 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17094
  have eq17125 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq17101
       grind)
    | exact superpose eq17101 eq179
    | exact resolve eq179 eq17101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17101
  have eq17139 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16654 eq17125
    | exact resolve eq17125 eq16654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16654 eq17125
  have eq17140 : x = (k y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq17139
  have eq17940 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16477 eq3028
    | exact resolve eq3028 eq16477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028 eq16477
  have eq17985 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17140 eq17940
    | exact resolve eq17940 eq17140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17940
  have eq17988 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17140 eq17985
    | exact resolve eq17985 eq17140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17985
  have eq17989 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq17988
  have eq18052 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17989 eq734
    | (have j0 := eq734 (σ x)
       grind)
    | (have r₁ := eq734 (σ x)
       have r₂ := eq17989
       grind)
    | exact resolve eq734 eq17989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17989
  have eq18055 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq18052
  have eq18076 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18055 eq1635
    | exact resolve eq1635 eq18055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq18122 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18055 eq18076
    | exact resolve eq18076 eq18055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18055 eq18076
  have eq18164 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18122 eq16504
    | exact resolve eq16504 eq18122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16504 eq18122
  have eq18182 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq18164
  have eq18193 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq18182
    | exact resolve eq18182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18182
  have eq18198 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17140 eq18193
    | exact resolve eq18193 eq17140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17140 eq18193
  have eq18213 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq18198
       grind)
    | exact superpose eq18198 eq36
    | exact resolve eq36 eq18198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq18223 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18213
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18213
    | exact resolve eq18213 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18213
  have eq18235 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18223 eq16409
    | exact resolve eq16409 eq18223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16409 eq18223
  have eq18250 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18235
  have eq18306 : y = (k x x) ∨ x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq18250
       grind)
    | exact superpose eq18250 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18311 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq18250
       grind)
    | exact superpose eq18250 eq178
    | exact resolve eq178 eq18250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18250
  have eq18328 : y = (k x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18306
  have eq18333 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18311
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18311
    | exact resolve eq18311 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18311
  have eq18354 : x = (k y y) ∨ x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq18333
       grind)
    | exact superpose eq18333 eq11
    | exact resolve eq11 eq18333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18360 : ∀ X0 : G, y = (M.op (M.op (M.op x x) X0) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq196 y y x
       have i₂ := eq18333
       grind)
    | exact superpose eq18333 eq196
    | exact resolve eq196 eq18333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18364 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1820 y y X0
       have i₂ := eq18333
       grind)
    | exact superpose eq18333 eq1820
    | exact resolve eq1820 eq18333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18368 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq18333
       grind)
    | exact superpose eq18333 eq179
    | exact resolve eq179 eq18333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18375 : x = (k y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18354
  have eq18378 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18368
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18368
    | exact resolve eq18368 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18368
  have eq18379 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18364 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18364
    | (have j0 := eq18364 X0
       grind)
    | exact resolve eq18364 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18364
  have eq18428 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq18378
       grind)
    | exact superpose eq18378 eq39
    | exact resolve eq39 eq18378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18434 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18428
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18428
    | exact resolve eq18428 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18428
  have eq18438 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18434
    | exact resolve eq18434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18434
  have eq18865 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq18375
       grind)
    | exact superpose eq18375 eq40
    | exact resolve eq40 eq18375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18375
  have eq18876 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18865
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18865
    | exact resolve eq18865 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18865
  have eq18881 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18876
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18876
    | exact resolve eq18876 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18876
  have eq18889 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18881 eq744
    | (have j0 := eq744 (σ y)
       grind)
    | exact resolve eq744 eq18881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18897 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18889
    | exact resolve eq18889 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18889
  have eq18903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18438 eq18897
    | exact resolve eq18897 eq18438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18897
  have eq18906 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18903
       have r₂ := eq27
       grind)
    | exact resolve eq18903 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18903
  have eq18933 : (k (σ y) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18906 eq564
    | exact resolve eq564 eq18906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18937 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18906 eq3030
    | exact resolve eq3030 eq18906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18938 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18937
  have eq18944 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18881 eq18938
    | exact resolve eq18938 eq18881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18938
  have eq18947 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18881 eq18933
    | exact resolve eq18933 eq18881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18881 eq18933
  have eq18957 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18944 eq18947
    | exact resolve eq18947 eq18944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18944 eq18947
  have eq19047 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18957 eq3030
    | exact resolve eq3030 eq18957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18957
  have eq19048 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19047
  have eq19079 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19048 eq141
    | exact resolve eq141 eq19048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19048
  have eq19090 : x = (k x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq19079
    | exact resolve eq19079 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19079
  have eq19143 : x ≠ x ∨ x = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq734 x
       have i₂ := eq19090
       grind)
    | exact superpose eq19090 eq734
    | (have j0 := eq734 x
       grind)
    | (have r₁ := eq734 x
       have r₂ := eq19090
       grind)
    | exact resolve eq734 eq19090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19090
  have eq19146 : x = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19143
  have eq19168 : (M.op x x) = (M.op (M.op x y) (M.op x x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1633 x
       have i₂ := eq19146
       grind)
    | exact superpose eq19146 eq1633
    | exact resolve eq1633 eq19146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19208 : x = (M.op (M.op x y) x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19146 eq19168
    | exact resolve eq19168 eq19146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19146 eq19168
  have eq19361 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19208 eq18379
    | exact resolve eq18379 eq19208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18379 eq19208
  have eq19383 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq19361
  have eq19392 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq19383
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19383
    | exact resolve eq19383 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19383
  have eq19393 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq19392
  have eq19397 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq19393 eq27
    | exact resolve eq27 eq19393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19430 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  have eq19561 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x x) x) := by
    first
    | (have i₁ := eq18360 (M.op x x)
       have i₂ := eq665 x
       grind)
    | exact superpose eq665 eq18360
    | (have j1 := eq665 x
       grind)
    | exact resolve eq18360 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18360
  have eq19614 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x x) x) := by
    first
    | (have i₁ := eq19561
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19561
    | exact resolve eq19561 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19561
  have eq19615 : x = (k (M.op x x) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19614
  have eq19627 : (σ x) = (k (σ (M.op x x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq19615
       grind)
    | exact superpose eq19615 eq39
    | exact resolve eq39 eq19615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19632 : (σ x) = (k (σ (M.op x x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19627
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19627
    | exact resolve eq19627 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19627
  have eq19659 : (τ (k (σ y) (σ x))) = (k y (k (M.op x x) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19632 eq111
    | exact resolve eq111 eq19632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq19632
  have eq19681 : (k y x) = (k y (k (M.op x x) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114 eq19659
    | exact resolve eq19659 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq19659
  have eq19689 : (M.op x y) = (k y (k (M.op x x) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18378 eq19681
    | exact resolve eq19681 eq18378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18378 eq19681
  have eq19691 : (M.op x y) = (k x (k (M.op x x) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19393 eq19689
    | exact resolve eq19689 eq19393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19689
  have eq19692 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19615 eq19691
    | exact resolve eq19691 eq19615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19615 eq19691
  have eq20839 : (τ (M.op (σ x) (σ y))) = (M.op y (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq685 y x
       have i₂ := eq16536
       grind)
    | exact superpose eq16536 eq685
    | (have j0 := eq685 y x
       grind)
    | exact resolve eq685 eq16536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16536
  have eq20990 : (τ (M.op (σ x) (σ y))) = (M.op y (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (k y x) := by grind
  clear eq20839
  have eq21017 : (τ (M.op (σ x) (σ y))) = (M.op y (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq20990
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq20990
       have r₂ := eq12 x y
       grind)
    | exact resolve eq20990 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20990
  have eq21034 : (τ (σ x)) = (M.op y (τ (σ x))) ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | exact superpose eq18198 eq21017
    | exact resolve eq21017 eq18198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18198 eq21017
  have eq21043 : x = (k y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq21034
    | exact resolve eq21034 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21034
  have eq21063 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq685 y x
       have i₂ := eq21043
       grind)
    | exact superpose eq21043 eq685
    | (have j0 := eq685 y x
       grind)
    | exact resolve eq685 eq21043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21064 : ∀ X0 : G, y = (M.op (M.op (M.op x x) X0) y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq686 y x X0
       have i₂ := eq21043
       grind)
    | exact superpose eq21043 eq686
    | (have j0 := eq686 y x x
       grind)
    | exact resolve eq686 eq21043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq21043
  have eq21065 : ∀ X0 : G, y = (M.op (M.op (M.op x x) X0) y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq21064 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21064
  have eq21066 : y = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq21063
  have eq21070 : ∀ X0 : G, y = (M.op (M.op (M.op x x) X0) y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq11 eq21065
    | (have j0 := eq21065 X0
       have j1 := eq11 y x
       grind)
    | exact resolve eq21065 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21065
  have eq21075 : ∀ X0 : G, y = (M.op (M.op (M.op x x) X0) y) ∨ x = (M.op y y) ∨ x = (k y x) := by
    intro X0
    first
    | (have j0 := eq21070 X0
       have j1 := eq12 y x
       grind)
    | (have r₁ := eq21070 X0
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq21070 X0
       have r₂ := eq12 x y
       grind)
    | exact resolve eq21070 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21070
  have eq21100 : (k x y) = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq21066
       grind)
    | exact superpose eq21066 eq179
    | exact resolve eq179 eq21066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21114 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq21066
       grind)
    | exact superpose eq21066 eq178
    | exact resolve eq178 eq21066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21066
  have eq21126 : x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21114
    | exact resolve eq21114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21114
  have eq21152 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq178 y y
       have i₂ := eq21126
       grind)
    | exact superpose eq21126 eq178
    | exact resolve eq178 eq21126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21126
  have eq21159 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq21152
  have eq21177 : ∀ X0 : G, (M.op x x) = (M.op (M.op y X0) (M.op x x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 y x x
       have i₂ := eq21159
       grind)
    | exact superpose eq21159 eq177
    | exact resolve eq177 eq21159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21178 : ∀ X0 : G, (M.op (M.op y X0) X0) = (M.op x (M.op (M.op y X0) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 y X0 x
       have i₂ := eq21159
       grind)
    | exact superpose eq21159 eq177
    | exact resolve eq177 eq21159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq21187 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1820 y x X0
       have i₂ := eq21159
       grind)
    | exact superpose eq21159 eq1820
    | exact resolve eq1820 eq21159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820 eq21159
  have eq21191 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21187 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21187
    | (have j0 := eq21187 X0
       grind)
    | exact resolve eq21187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21187
  have eq21195 : y = (M.op (k x (M.op x x)) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2376 eq21191
    | exact resolve eq21191 eq2376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2376 eq21191
  have eq21494 : y = (M.op (k x (k x x)) y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21195
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq21195
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq21195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21513 : y = (M.op (k x (k x x)) y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq21494
  have eq21607 : ∀ X0 : G, (k x x) = (M.op (M.op y X0) (k x x)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq21177 X0
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq21177
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq21177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21632 : ∀ X0 : G, (k x x) = (M.op (M.op y X0) (k x x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21607
  have eq21826 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op (M.op y X0) X0) X1) X1) x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1674 x (M.op (M.op y X0) X0) X1
       have i₂ := eq21178 X0
       grind)
    | exact superpose eq21178 eq1674
    | exact resolve eq1674 eq21178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674 eq21178
  have eq22413 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op (M.op y X0) (M.op y X0)) X1) X1) x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq21826 (M.op y X0) X1
       have i₂ := eq178 y X0
       grind)
    | exact superpose eq178 eq21826
    | exact resolve eq21826 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21826
  have eq25417 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op (M.op (M.op y X0) X1) X1) X2) x) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22413 X0 (M.op (M.op (M.op (M.op y X0) X1) X1) X2)
       have i₂ := eq176 (M.op y X0) X1 X2 (M.op (M.op (M.op (M.op y X0) X1) X1) X2)
       grind)
    | exact superpose eq176 eq22413
    | exact resolve eq22413 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22413
  have eq25497 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op (M.op (M.op y X0) X0) X1) X2) x) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25417 y (M.op (M.op (M.op y X0) X0) X1) X2
       have i₂ := eq176 y X0 X1 (M.op (M.op (M.op y X0) X0) X1)
       grind)
    | exact superpose eq176 eq25417
    | exact resolve eq25417 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq25539 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op x (M.op (M.op y X0) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq196 (M.op (M.op y X0) X1) X1 x
       have i₂ := eq25417 X0 X1 (M.op (M.op (M.op y X0) X1) X1)
       grind)
    | exact superpose eq25417 eq196
    | exact resolve eq196 eq25417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25417
  have eq25649 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op x x) X0) X1) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq25497 (M.op x x) X0 X1
       have i₂ := eq21177 (M.op x x)
       grind)
    | exact superpose eq21177 eq25497
    | exact resolve eq25497 eq21177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21177 eq25497
  have eq25722 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op x x) X0) X1) x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq25649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25649
  have eq25742 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (k x x) X0) X1) x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq25722 X0 X1
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq25722
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq25722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25722
  have eq25821 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (k x x) X0) X1) x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq25742 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25742
  have eq25953 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k (M.op y y) y) := by
    first
    | (have i₁ := eq25539 y (M.op y y)
       have i₂ := eq665 y
       grind)
    | exact superpose eq665 eq25539
    | (have j1 := eq665 y
       grind)
    | exact resolve eq25539 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq26012 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k (M.op y y) y) := by
    first
    | (have i₁ := eq25953
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25953
    | exact resolve eq25953 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25953
  have eq26013 : y = (k (M.op y y) y) ∨ y = (M.op x y) := by grind
  clear eq26012
  have eq26015 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26013
       have i₂ := eq18333
       grind)
    | exact superpose eq18333 eq26013
    | exact resolve eq26013 eq18333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26020 : (σ y) = (k (σ (M.op y y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq26013
       grind)
    | exact superpose eq26013 eq40
    | exact resolve eq40 eq26013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26013
  have eq26023 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26015
  have eq26025 : (σ y) = (k (σ (M.op y y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26020
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26020
    | exact resolve eq26020 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26020
  have eq26028 : x = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19393 eq26023
    | exact resolve eq26023 eq19393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26023
  have eq26030 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19692 eq26028
    | exact resolve eq26028 eq19692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19692 eq26028
  have eq26054 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26025
       have i₂ := eq18333
       grind)
    | exact superpose eq18333 eq26025
    | exact resolve eq26025 eq18333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18333 eq26025
  have eq26075 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26054
  have eq26092 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26075
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26075
    | exact resolve eq26075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26075
  have eq26140 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26092 eq723
    | exact resolve eq723 eq26092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq26092
  have eq26146 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26140
  have eq41036 : x = (M.op y y) ∨ x = (k y x) ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq752 x x y
       have i₂ := eq21075 x
       grind)
    | exact superpose eq21075 eq752
    | exact resolve eq752 eq21075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq21075
  have eq41070 : x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq41036
  have eq47103 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq18328
       grind)
    | exact superpose eq18328 eq39
    | exact resolve eq39 eq18328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18328
  have eq47123 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47103
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47103
    | exact resolve eq47103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47103
  have eq47128 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47123
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47123
    | exact resolve eq47123 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47123
  have eq47133 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19393 eq47128
    | exact resolve eq47128 eq19393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19393 eq47128
  have eq47841 : (k x x) = (M.op x (k x x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25539 x (k x x)
       have i₂ := eq21632 x
       grind)
    | exact superpose eq21632 eq25539
    | exact resolve eq25539 eq21632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21632
  have eq47901 : (k x x) = (M.op x (k x x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq47841
  have eq49516 : (k x x) = (k x (k x x)) ∨ (k x x) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq762 x (k x x)
       have i₂ := eq47901
       grind)
    | exact superpose eq47901 eq762
    | exact resolve eq762 eq47901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq47901
  have eq49561 : (k x x) = (k x (k x x)) ∨ (k x x) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq49516
       have r₂ := eq13 x (k x x)
       grind)
    | (have r₁ := eq49516
       have r₂ := eq13 x x
       grind)
    | exact resolve eq49516 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49516
  have eq50237 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47133 eq685
    | (have j0 := eq685 (σ x) (σ x)
       grind)
    | exact resolve eq685 eq47133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50240 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50237
  have eq50246 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq50240
    | exact resolve eq50240 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50240
  have eq50247 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50246
  have eq50789 : (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50247 eq564
    | exact resolve eq564 eq50247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq50247
  have eq50836 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47133 eq50789
    | exact resolve eq50789 eq47133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47133 eq50789
  have eq50849 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq50836
    | exact resolve eq50836 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50836
  have eq50850 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50849
  have eq50943 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50850 eq179
    | exact resolve eq179 eq50850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50957 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50850 eq11
    | exact resolve eq11 eq50850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50850
  have eq50975 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50957
  have eq50998 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26030 eq50975
    | exact resolve eq50975 eq26030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26030 eq50975
  have eq50999 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50998
  have eq51003 : (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq181 eq50943
    | exact resolve eq50943 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq50943
  have eq51151 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50999 eq41
    | exact resolve eq41 eq50999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq50999
  have eq51174 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq51151
    | exact resolve eq51151 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51151
  have eq51180 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51174
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51174
    | exact resolve eq51174 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51174
  have eq51197 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51003 eq39
    | exact resolve eq39 eq51003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51003
  have eq51202 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq51197
    | exact resolve eq51197 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51197
  have eq69261 : y = (M.op (k x x) y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (k x x) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21513
       have i₂ := eq49561
       grind)
    | exact superpose eq49561 eq21513
    | exact resolve eq21513 eq49561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21513 eq49561
  have eq69272 : y = (M.op (k x x) y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (k x x) = (M.op x x) := by grind
  clear eq69261
  have eq69281 : y = (M.op (k x x) y) ∨ y = (M.op x y) ∨ (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq69272
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq69272
       have r₂ := eq13 x (k x x)
       grind)
    | exact resolve eq69272 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69272
  have eq69295 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq25821 y X0
       have i₂ := eq69281
       grind)
    | exact superpose eq69281 eq25821
    | exact resolve eq25821 eq69281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25821 eq69281
  have eq69325 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq69295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69295
  have eq69332 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) ∨ (k x x) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq69325 X0
       have j1 := eq13 x x
       grind)
    | (have r₁ := eq69325 X0
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq69325 X0
       have r₂ := eq13 x (k x x)
       grind)
    | exact resolve eq69325 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69325
  have eq69595 : x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq25539 x x
       have i₂ := eq69332 x
       grind)
    | exact superpose eq69332 eq25539
    | exact resolve eq25539 eq69332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25539 eq69332
  have eq69669 : x = (M.op x x) ∨ y = (M.op x y) ∨ (k x x) = (M.op x x) := by grind
  clear eq69595
  have eq69696 : (k x x) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq69669
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq69669
       have r₂ := eq13 x (k x x)
       grind)
    | exact resolve eq69669 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69669
  have eq69737 : y = (M.op (k x (k x x)) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21195
       have i₂ := eq69696
       grind)
    | exact superpose eq69696 eq21195
    | exact resolve eq21195 eq69696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21195
  have eq69845 : (k x x) = (M.op x (k x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq69696
       grind)
    | exact superpose eq69696 eq178
    | exact resolve eq178 eq69696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69913 : y = (M.op (k x (k x x)) y) ∨ y = (M.op x y) := by grind
  clear eq69737
  have eq79914 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26146 eq178
    | exact resolve eq178 eq26146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq26146
  have eq79961 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq79914
    | exact resolve eq79914 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79914
  have eq79962 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq79961
  have eq80011 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq79962 eq179
    | exact resolve eq179 eq79962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79962
  have eq80083 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq80011
    | exact resolve eq80011 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80011
  have eq80094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18438 eq80083
    | exact resolve eq80083 eq18438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18438 eq80083
  have eq80097 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq80094
       have r₂ := eq27
       grind)
    | exact resolve eq80094 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80094
  have eq80113 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80097 eq781
    | exact resolve eq781 eq80097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq80144 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq80146 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq80113
    | exact resolve eq80113 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80113
  have eq80925 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80146 eq11
    | exact resolve eq11 eq80146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80146
  have eq80950 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq80925
  have eq80975 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq80950
       have r₂ := eq80144
       grind)
    | exact resolve eq80950 eq80144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80144 eq80950
  have eq81004 : (τ (σ y)) = (k x x) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80975 eq97
    | exact resolve eq97 eq80975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq80975
  have eq81057 : y = (k x y) ∨ y = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq81004
    | exact resolve eq81004 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81004
  have eq81117 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ y = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq714
       have i₂ := eq81057
       grind)
    | exact superpose eq81057 eq714
    | exact resolve eq714 eq81057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq81057
  have eq81129 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81117
  have eq81141 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (k x x) ∨ y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69696 eq81129
    | exact resolve eq81129 eq69696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69696 eq81129
  have eq81142 : y = (k x x) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81141
  have eq81230 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69845
       have i₂ := eq81142
       grind)
    | exact superpose eq81142 eq69845
    | exact resolve eq69845 eq81142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69845 eq81142
  have eq81291 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81230
  have eq81337 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81291
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81291
    | exact resolve eq81291 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81291
  have eq81338 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81337
  have eq81446 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq81338
       grind)
    | exact superpose eq81338 eq179
    | exact resolve eq179 eq81338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq81460 : x = (k y y) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq81338
       grind)
    | exact superpose eq81338 eq11
    | exact resolve eq11 eq81338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81338
  have eq81485 : x = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81460
  have eq81568 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81446
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81446
    | exact resolve eq81446 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81446
  have eq81626 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq81568
       grind)
    | exact superpose eq81568 eq39
    | exact resolve eq39 eq81568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq81568
  have eq81640 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81626
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq81626
    | exact resolve eq81626 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81626
  have eq81647 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq81640
    | exact resolve eq81640 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81640
  have eq81735 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq81485
       grind)
    | exact superpose eq81485 eq40
    | exact resolve eq40 eq81485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq81485
  have eq81762 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81735
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq81735
    | exact resolve eq81735 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81735
  have eq81769 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81762
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq81762
    | exact resolve eq81762 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81762
  have eq85785 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81769 eq744
    | (have j0 := eq744 (σ y)
       grind)
    | exact resolve eq744 eq81769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85806 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq85785
    | exact resolve eq85785 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85785
  have eq85814 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18906 eq85806
    | exact resolve eq85806 eq18906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18906 eq85806
  have eq85817 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81647 eq85814
    | exact resolve eq85814 eq81647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81647 eq85814
  have eq85818 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq85817
       have r₂ := eq19397
       grind)
    | exact resolve eq85817 eq19397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19397 eq85817
  have eq85858 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq85818 eq3030
    | exact resolve eq3030 eq85818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85818
  have eq85888 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq85858
  have eq85923 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81769 eq85888
    | exact resolve eq85888 eq81769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81769 eq85888
  have eq85949 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq85923
       have r₂ := eq19430
       grind)
    | exact resolve eq85923 eq19430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19430 eq85923
  have eq85963 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq85949 eq185
    | exact resolve eq185 eq85949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85949
  have eq86105 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq85963 eq3030
    | exact resolve eq3030 eq85963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85963
  have eq86135 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq86105
  have eq86220 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq86135 eq141
    | exact resolve eq141 eq86135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86135
  have eq86253 : x = (k x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq86220
    | exact resolve eq86220 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86220
  have eq86311 : y = (M.op (k x x) y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq69913
       have i₂ := eq86253
       grind)
    | exact superpose eq86253 eq69913
    | exact resolve eq69913 eq86253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69913
  have eq86342 : y = (M.op (k x x) y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq86311
  have eq86401 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq86253 eq86342
    | exact resolve eq86342 eq86253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86253 eq86342
  have eq86412 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq86401
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86401
    | exact resolve eq86401 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86401
  have eq86413 : y = (M.op x y) ∨ x = y := by grind
  clear eq86412
  have eq86419 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq86413
       grind)
    | exact superpose eq86413 eq24
    | exact resolve eq24 eq86413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86499 : x ≠ (M.op x y) ∨ x = y := by grind
  have eq86525 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq86419
    | exact resolve eq86419 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86419
  have eq86596 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq86525 eq51180
    | exact resolve eq51180 eq86525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51180
  have eq86598 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq86525 eq51202
    | exact resolve eq51202 eq86525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51202
  have eq86633 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq86598
  have eq86646 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80097 eq86633
    | exact resolve eq86633 eq80097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86633
  have eq86648 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq86596
       have r₂ := eq86499
       grind)
    | exact resolve eq86596 eq86499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86596
  have eq86703 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80097 eq86648
    | exact resolve eq86648 eq80097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80097 eq86648
  have eq88598 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq86703 eq744
    | (have j0 := eq744 (σ y)
       grind)
    | exact resolve eq744 eq86703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq88618 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq88598
    | exact resolve eq88598 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88598
  have eq88625 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq86646 eq88618
    | exact resolve eq88618 eq86646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86646 eq88618
  have eq88626 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq88625
  have eq91803 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88626 eq3030
    | exact resolve eq3030 eq88626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88626
  have eq91836 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq91803
  have eq91878 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq86703 eq91836
    | exact resolve eq91836 eq86703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86703 eq91836
  have eq91913 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq91878 eq27
    | exact resolve eq27 eq91878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91878
  have eq91966 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq86525 eq91913
    | (have r₁ := eq91913
       have r₂ := eq86525
       grind)
    | exact resolve eq91913 eq86525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91913
  have eq91967 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq91966
  have eq91968 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq91967
       have r₂ := eq86499
       grind)
    | exact resolve eq91967 eq86499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91967
  have eq91980 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq91968 eq185
    | exact resolve eq185 eq91968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq92133 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq91980 eq3030
    | exact resolve eq3030 eq91980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91980
  have eq92166 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq92133
  have eq92248 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq92166 eq141
    | exact resolve eq141 eq92166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq92166
  have eq92280 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq92248
    | exact resolve eq92248 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92248
  have eq92363 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq685 x x
       have i₂ := eq92280
       grind)
    | exact superpose eq92280 eq685
    | (have j0 := eq685 x x
       grind)
    | exact resolve eq685 eq92280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq92280
  have eq92366 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq92363
  have eq92476 : (M.op x x) = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1633 x
       have i₂ := eq92366
       grind)
    | exact superpose eq92366 eq1633
    | exact resolve eq1633 eq92366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92627 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq92366 eq92476
    | exact resolve eq92476 eq92366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92476
  have eq92735 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x x) X0) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq92627 eq196
    | exact resolve eq196 eq92627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq92627
  have eq92783 : ∀ X0 : G, (M.op x y) = (M.op (M.op x X0) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq92366 eq92735
    | exact resolve eq92735 eq92366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92735
  have eq93686 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq92783 eq1633
    | (have j1 := eq92783 y
       grind)
    | exact resolve eq1633 eq92783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633 eq92783
  have eq93968 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq93686 eq3030
    | exact resolve eq3030 eq93686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3030
  have eq94001 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq93968
  have eq94080 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq94001 eq779
    | (have j0 := eq779 (M.op x y)
       grind)
    | exact resolve eq779 eq94001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq94001
  have eq94098 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq94080
  have eq94108 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq94098
    | exact resolve eq94098 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94098
  have eq94116 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq86525 eq94108
    | exact resolve eq94108 eq86525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86525 eq94108
  have eq94138 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq94116 eq16376
    | exact resolve eq16376 eq94116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16376 eq94116
  have eq94211 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq94138
  have eq94244 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq86413 eq94211
    | exact resolve eq94211 eq86413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94211
  have eq94256 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq86413 eq94244
    | exact resolve eq94244 eq86413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86413 eq94244
  have eq94263 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq91968 eq94256
    | exact resolve eq94256 eq91968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91968 eq94256
  have eq94264 : (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq94263
  have eq94272 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq93686 eq94264
    | exact resolve eq94264 eq93686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93686 eq94264
  have eq94276 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq94272
       have r₂ := eq86499
       grind)
    | exact resolve eq94272 eq86499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94272
  have eq94418 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq92366
       have i₂ := eq94276
       grind)
    | exact superpose eq94276 eq92366
    | exact resolve eq92366 eq94276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92366 eq94276
  have eq94538 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq94418
  have eq94567 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq94538
       have r₂ := eq86499
       grind)
    | exact resolve eq94538 eq86499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86499 eq94538
  have eq94576 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq94567 eq31
    | exact resolve eq31 eq94567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq94567
  have eq94816 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq94576
    | exact resolve eq94576 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq94576
  have eq94817 : x = y := by grind
  clear eq94816
  have eq94877 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq94817
       grind)
    | exact superpose eq94817 eq18
    | exact resolve eq18 eq94817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq94878 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq94817
       grind)
    | exact superpose eq94817 eq24
    | exact resolve eq24 eq94817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq94945 : (k x x) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21100
       have i₂ := eq94817
       grind)
    | exact superpose eq94817 eq21100
    | exact resolve eq21100 eq94817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21100
  have eq95067 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41070
       have i₂ := eq94817
       grind)
    | exact superpose eq94817 eq41070
    | exact resolve eq41070 eq94817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41070 eq94817
  have eq95117 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq94945
  have eq95143 : x = (M.op x x) := by
    first
    | (have j1 := eq734 x
       grind)
    | (have r₁ := eq95067
       have r₂ := eq734 x
       grind)
    | exact resolve eq95067 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq95067
  have eq95151 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq95117
       have r₂ := eq13 x (k x x)
       grind)
    | (have r₁ := eq95117
       have r₂ := eq13 x x
       grind)
    | exact resolve eq95117 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95117
  have eq95194 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq94878
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94878
    | exact resolve eq94878 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94878
  have eq95196 : x = (M.op x y) := by
    first
    | (have i₁ := eq95143
       have i₂ := eq94877
       grind)
    | exact superpose eq94877 eq95143
    | exact resolve eq95143 eq94877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95143
  have eq95201 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq95151
       have i₂ := eq94877
       grind)
    | exact superpose eq94877 eq95151
    | exact resolve eq95151 eq94877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94877 eq95151
  have eq95220 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq95201
       have i₂ := eq95196
       grind)
    | exact superpose eq95196 eq95201
    | exact resolve eq95201 eq95196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95201
  have eq95224 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq95194 eq26
    | exact resolve eq26 eq95194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq95194
  have eq95532 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq95196
       grind)
    | exact superpose eq95196 eq22
    | exact resolve eq22 eq95196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq95196
  have eq96194 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq95532 eq20
    | exact resolve eq20 eq95532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95532
  have eq100286 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq95220 eq37
    | exact resolve eq37 eq95220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq95220
  have eq100321 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq100286
    | exact resolve eq100286 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq100286
  have eq100329 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq96194 eq100321
    | exact resolve eq100321 eq96194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100321
  have eq100425 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95224 eq11
    | exact resolve eq11 eq95224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95224
  have eq100456 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq100425
  have eq100471 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq100329 eq100456
    | exact resolve eq100456 eq100329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100329 eq100456
  have eq100472 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq100471
  have eq100483 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq100472 eq27
    | exact resolve eq27 eq100472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq100472
  have eq100552 : False := by grind
  exact eq100552

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation3081 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq341 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq366 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq341 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq367 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq373 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq367 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq367 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq367 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq381 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq373
    | (have j0 := eq373 X0 X1
       grind)
    | exact resolve eq373 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq382 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq387 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq382 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq382
    | exact resolve eq382 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq382 x y
       grind)
    | exact superpose eq382 eq16
    | exact resolve eq16 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq484 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq387 X0 (τ X1)
       grind)
    | exact superpose eq387 eq17
    | exact resolve eq17 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq387
  have eq500 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq484
    | exact resolve eq484 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq507 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq500 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq500
    | exact resolve eq500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq519 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq399
       have i₂ := eq507 x y
       grind)
    | exact superpose eq507 eq399
    | exact resolve eq399 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq507
  have eq520 : False := by grind
  exact eq520

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyy_x_pyx_Equation3081 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3081 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) X1 X0
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : x ≠ (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq65 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq76 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq115
  have eq134 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq145 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq134 eq16
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq214 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq219 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq214 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq214
       grind)
    | exact resolve eq12 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq219
  have eq224 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq229 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq224 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq224
       grind)
    | exact resolve eq12 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq229
  have eq252 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1001
    | exact resolve eq1001 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1005 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1002
       have r₂ := eq27
       grind)
    | exact resolve eq1002 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1007 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1005
    | exact resolve eq1005 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1009 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1007
    | exact resolve eq1007 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1011 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1009 eq27
    | exact resolve eq27 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1019 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1009 eq232
    | exact resolve eq232 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1009
  have eq1129 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1019
       have r₂ := eq1022
       grind)
    | exact resolve eq1019 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq1022
  have eq1132 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1129 eq116
    | exact resolve eq116 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1133 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1129 eq84
    | exact resolve eq84 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1136 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1132
  have eq1140 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1133
    | exact resolve eq1133 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1133
  have eq1141 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1136
       have r₂ := eq1011
       grind)
    | exact resolve eq1136 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011 eq1136
  have eq1144 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1140
       have r₂ := eq76
       grind)
    | exact resolve eq1140 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1140
  have eq1146 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1141 eq27
    | exact resolve eq27 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1141 eq65
    | (have r₁ := eq65
       have r₂ := eq1141
       grind)
    | exact resolve eq65 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1150 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1141 eq224
    | exact resolve eq224 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1156 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1148
  have eq1179 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1144
       grind)
    | exact superpose eq1144 eq73
    | exact resolve eq73 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1184 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1179
    | exact resolve eq1179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1224 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1184 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1225 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1224
  have eq1229 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1225
    | exact resolve eq1225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1232 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1229
    | exact resolve eq1229 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1233 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1232
  have eq1236 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1233 eq27
    | exact resolve eq27 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1394 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1156 eq116
    | exact resolve eq116 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1156
  have eq1397 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1394
  have eq1410 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1397 eq1150
    | exact resolve eq1150 eq1397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq1397
  have eq1427 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1410
  have eq1429 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1427
       have r₂ := eq1146
       grind)
    | exact resolve eq1427 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146 eq1427
  have eq1431 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1429 eq20
    | exact resolve eq20 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1464 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1431
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1431
    | exact resolve eq1431 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1431
  have eq1515 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1464 eq84
    | exact resolve eq84 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1527 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1464 eq1236
    | (have r₁ := eq1236
       have r₂ := eq1464
       grind)
    | exact resolve eq1236 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236 eq1464
  have eq1530 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1527
  have eq1531 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1530
  have eq1543 : (k y x) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq145 eq1515
    | exact resolve eq1515 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq1515
  have eq1596 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1531 eq27
    | exact resolve eq27 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1598 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1531 eq65
    | (have r₁ := eq65
       have r₂ := eq1531
       grind)
    | exact resolve eq65 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1600 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1531 eq224
    | exact resolve eq224 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq1531
  have eq1607 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1598
  have eq2163 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1543 eq222
    | exact resolve eq222 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq1543
  have eq2166 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq2163
  have eq2172 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq2166
       grind)
    | exact superpose eq2166 eq73
    | exact resolve eq73 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166
  have eq2176 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2172
    | exact resolve eq2172 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172
  have eq2724 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1607 eq2176
    | exact resolve eq2176 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607 eq2176
  have eq2728 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2724
  have eq2850 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2728 eq1600
    | exact resolve eq1600 eq2728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600 eq2728
  have eq2869 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2850
  have eq2872 : x = (M.op x y) := by
    first
    | (have r₁ := eq2869
       have r₂ := eq1596
       grind)
    | exact resolve eq2869 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596 eq2869
  have eq2875 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2872 eq20
    | exact resolve eq20 eq2872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2878 : x ≠ x ∨ (k y x) = (M.op x x) := by
    first
    | exact superpose eq2872 eq64
    | (have r₁ := eq64
       have r₂ := eq2872
       grind)
    | exact resolve eq64 eq2872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2885 : x = (M.op x x) := by
    first
    | exact superpose eq2872 eq214
    | exact resolve eq214 eq2872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq2872
  have eq2898 : (k y x) = (M.op x x) := by grind
  clear eq2878
  have eq2913 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2875
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2875
    | exact resolve eq2875 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2875
  have eq2919 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2913 eq26
    | exact resolve eq26 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2933 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2913 eq232
    | exact resolve eq232 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq2958 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2933
       have r₂ := eq27
       grind)
    | exact resolve eq2933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2933
  have eq2977 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq252 x x
       have i₂ := eq2885
       grind)
    | exact superpose eq2885 eq252
    | (have r₁ := eq252 x x
       have r₂ := eq2885
       grind)
    | exact resolve eq252 eq2885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq2981 : x = (k x x) := by grind
  clear eq2977
  have eq3040 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2981
       grind)
    | exact superpose eq2981 eq43
    | exact resolve eq43 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2981
  have eq3044 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2913 eq3040
    | exact resolve eq3040 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq3045 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3044
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3044
    | exact resolve eq3044 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044
  have eq3046 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2913 eq3045
    | exact resolve eq3045 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq3101 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3046 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq3046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046
  have eq3102 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3101
  have eq3218 : x = (k y x) := by
    first
    | (have i₁ := eq2898
       have i₂ := eq2885
       grind)
    | exact superpose eq2885 eq2898
    | exact resolve eq2898 eq2885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2885 eq2898
  have eq3231 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq3218
       grind)
    | exact superpose eq3218 eq73
    | exact resolve eq73 eq3218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq3218
  have eq3238 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2913 eq3231
    | exact resolve eq3231 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231
  have eq3240 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3238
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3238
    | exact resolve eq3238 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3238
  have eq3241 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2913 eq3240
    | exact resolve eq3240 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2913 eq3240
  have eq3249 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3241 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq3241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3250 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq3249
  have eq3252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2919 eq3250
    | exact resolve eq3250 eq2919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3250
  have eq3255 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq3252
       have r₂ := eq27
       grind)
    | exact resolve eq3252 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252
  have eq3258 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2919 eq3255
    | exact resolve eq3255 eq2919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3255
  have eq3278 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq3258 eq2958
    | exact resolve eq2958 eq3258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958 eq3258
  have eq3282 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3241 eq3278
    | exact resolve eq3278 eq3241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3241 eq3278
  have eq3331 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3282 eq2919
    | exact resolve eq2919 eq3282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919 eq3282
  have eq3337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3102 eq3331
    | exact resolve eq3331 eq3102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102 eq3331
  have eq3350 : False := by grind
  exact eq3350

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation3081 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3081 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq86 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq9881
    | exact resolve eq9881 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9881
  have eq9893 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq9882
       have r₂ := eq28
       grind)
    | exact resolve eq9882 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9882
  have eq9897 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq9893
    | exact resolve eq9893 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9893
  have eq10267 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9897 eq87
    | (have r₁ := eq87
       have r₂ := eq9897
       grind)
    | exact resolve eq87 eq9897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq9897
  have eq10313 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq10267
  have eq10314 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq10313
  have eq10321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq10314 eq78
    | exact resolve eq78 eq10314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq10314
  have eq10331 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10321
  have eq10334 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10331
       have r₂ := eq28
       grind)
    | exact resolve eq10331 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10331
  have eq10572 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq10334
       grind)
    | exact superpose eq10334 eq52
    | exact resolve eq52 eq10334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq10574 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq10334
       grind)
    | exact superpose eq10334 eq86
    | (have r₁ := eq86
       have r₂ := eq10334
       grind)
    | exact resolve eq86 eq10334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq10334
  have eq10620 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq10574
  have eq10621 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10620
  have eq10633 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq10572
    | exact resolve eq10572 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10572
  have eq10642 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq10621
       grind)
    | exact superpose eq10621 eq49
    | exact resolve eq49 eq10621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq10621
  have eq10660 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq10642
    | exact resolve eq10642 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10642
  have eq11020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10660 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq10660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10660
  have eq11021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11020
  have eq11025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq11021
    | exact resolve eq11021 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11021
  have eq11036 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11025
       have r₂ := eq28
       grind)
    | exact resolve eq11025 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11025
  have eq11040 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq11036
    | exact resolve eq11036 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11036
  have eq11271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11040 eq10633
    | exact resolve eq10633 eq11040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10633 eq11040
  have eq11312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11271
  have eq11317 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11312
       have r₂ := eq28
       grind)
    | exact resolve eq11312 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11312
  have eq11320 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq11317 eq30
    | exact resolve eq30 eq11317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11317
  have eq11427 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq11320
    | exact resolve eq11320 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11320
  have eq11428 : x = y := by grind
  clear eq11427
  have eq11526 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq11428
       grind)
    | exact superpose eq11428 eq19
    | exact resolve eq19 eq11428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq11527 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq11428
       grind)
    | exact superpose eq11428 eq25
    | exact resolve eq25 eq11428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11428
  have eq11636 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11527
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11527
    | exact resolve eq11527 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11527
  have eq11651 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11636 eq27
    | exact resolve eq27 eq11636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11636
  have eq11874 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11651 eq69
    | exact resolve eq69 eq11651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq11651
  have eq11936 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11874
       have i₂ := eq11526
       grind)
    | exact superpose eq11526 eq11874
    | exact resolve eq11874 eq11526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11526 eq11874
  have eq11945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11936 eq15
    | exact resolve eq15 eq11936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11936
  have eq11992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11945
    | exact resolve eq11945 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq11945
  have eq12001 : False := by grind
  exact eq12001

/-- `Equation3081`: `x = (((x ◇ y) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation3081 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3081 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3081.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (M.op x x) = (k y x) := by
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
  have eq82 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq10452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq10452
    | exact resolve eq10452 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10452
  have eq10464 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq10453
       have r₂ := eq28
       grind)
    | exact resolve eq10453 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10453
  have eq10468 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq10464
    | exact resolve eq10464 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10464
  have eq10473 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq10468 eq82
    | (have r₁ := eq82
       have r₂ := eq10468
       grind)
    | exact resolve eq82 eq10468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq10468
  have eq10519 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq10473
  have eq10520 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq10519
  have eq10763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq10520 eq103
    | exact resolve eq103 eq10520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq10520
  have eq10773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10763
  have eq10776 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10773
       have r₂ := eq28
       grind)
    | exact resolve eq10773 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10773
  have eq10778 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq10776
       grind)
    | exact superpose eq10776 eq52
    | exact resolve eq52 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq10780 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq10776
       grind)
    | exact superpose eq10776 eq81
    | (have r₁ := eq81
       have r₂ := eq10776
       grind)
    | exact resolve eq81 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq10776
  have eq10826 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq10780
  have eq10827 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10826
  have eq10839 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq10778
    | exact resolve eq10778 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10778
  have eq11090 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq10827
       grind)
    | exact superpose eq10827 eq88
    | exact resolve eq88 eq10827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq10827
  have eq11108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq11090
    | exact resolve eq11090 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11090
  have eq11441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11108
  have eq11442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11441
  have eq11446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq11442
    | exact resolve eq11442 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11442
  have eq11457 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11446
       have r₂ := eq28
       grind)
    | exact resolve eq11446 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11446
  have eq11461 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq11457
    | exact resolve eq11457 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11457
  have eq11558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11461 eq10839
    | exact resolve eq10839 eq11461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10839 eq11461
  have eq11599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11558
  have eq11604 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11599
       have r₂ := eq28
       grind)
    | exact resolve eq11599 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11599
  have eq11607 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq11604 eq30
    | exact resolve eq30 eq11604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11604
  have eq11718 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq11607
    | exact resolve eq11607 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11607
  have eq11719 : x = y := by grind
  clear eq11718
  have eq11738 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq11719
       grind)
    | exact superpose eq11719 eq19
    | exact resolve eq19 eq11719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq11739 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq11719
       grind)
    | exact superpose eq11719 eq25
    | exact resolve eq25 eq11719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11719
  have eq11848 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11739
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11739
    | exact resolve eq11739 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11739
  have eq11947 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11848 eq27
    | exact resolve eq27 eq11848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11848
  have eq12178 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11947 eq69
    | exact resolve eq69 eq11947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq11947
  have eq12242 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12178
       have i₂ := eq11738
       grind)
    | exact superpose eq11738 eq12178
    | exact resolve eq12178 eq11738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11738 eq12178
  have eq12639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12242 eq15
    | exact resolve eq15 eq12242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12242
  have eq12686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12639
    | exact resolve eq12639 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq12639
  have eq12695 : False := by grind
  exact eq12695

/-- `Equation3089`: `x = (((x ◇ y) ◇ z) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyx_pxy_Equation3089 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3089 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3089.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X1) X0) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) y) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) X0 X1
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq81
    | exact resolve eq81 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq91 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq101 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq214 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq224 : (M.op x y) ≠ (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq214 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq214
       grind)
    | exact resolve eq13 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : x = (k (M.op x y) x) := by grind
  clear eq224
  have eq228 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq225 eq130
    | exact resolve eq130 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq225
  have eq232 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq228
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq228
    | exact resolve eq228 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq235 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq232 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq235
  have eq239 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq249 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq239 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq239
       grind)
    | exact resolve eq13 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq250 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq249
  have eq264 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq271 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq845 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq69 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq845 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq859 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq856 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq856 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq856 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq856 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq870 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq859 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq859
    | (have j0 := eq859 X0 X1
       grind)
    | exact resolve eq859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq949 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq236 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq236
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op x y))
       have r₂ := eq236
       grind)
    | exact resolve eq12 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq958 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq949
  have eq959 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq958
  have eq960 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq232 eq959
    | exact resolve eq959 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq959
  have eq1014 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq960 eq60
    | exact resolve eq60 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq960
  have eq9691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq9692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq9691
    | exact resolve eq9691 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9691
  have eq9703 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq9692
       have r₂ := eq27
       grind)
    | exact resolve eq9692 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9692
  have eq9706 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq9703
    | exact resolve eq9703 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9703
  have eq9725 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9706 eq270
    | exact resolve eq270 eq9706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq9706
  have eq9747 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9725 eq55
    | exact resolve eq55 eq9725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq9725
  have eq9772 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq9747
    | exact resolve eq9747 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9747
  have eq9775 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq9772
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq9772
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq9772
       have r₂ := eq13 x y
       grind)
    | exact resolve eq9772 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9772
  have eq10541 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq853 x y
       have i₂ := eq9775
       grind)
    | exact superpose eq9775 eq853
    | (have j0 := eq853 x y
       grind)
    | exact resolve eq853 eq9775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10543 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq9775
       grind)
    | exact superpose eq9775 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq9775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9775
  have eq10544 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10543
  have eq10546 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10541
  have eq10550 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10544
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10544
    | exact resolve eq10544 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10544
  have eq10551 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10550
  have eq10553 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10546
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10546
    | exact resolve eq10546 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10546
  have eq10566 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10553
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10553
    | exact resolve eq10553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10553
  have eq10570 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10566
    | exact resolve eq10566 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10566
  have eq10571 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq10570
  have eq10576 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10571
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10571
    | exact resolve eq10571 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10571
  have eq10580 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10576
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10576
    | exact resolve eq10576 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10576
  have eq10592 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq271 y x
       have i₂ := eq10551
       grind)
    | exact superpose eq10551 eq271
    | exact resolve eq271 eq10551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10551
  have eq10602 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10592
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10592
    | exact resolve eq10592 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10592
  have eq10606 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10602
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10602
    | exact resolve eq10602 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10602
  have eq10607 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10606
  have eq10657 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10580 eq271
    | exact resolve eq271 eq10580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10580
  have eq10667 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10657
    | exact resolve eq10657 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10657
  have eq10671 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10667
    | exact resolve eq10667 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10667
  have eq10672 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10671
  have eq10675 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq10607
       grind)
    | exact superpose eq10607 eq91
    | exact resolve eq91 eq10607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq10607
  have eq10697 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10675
    | exact resolve eq10675 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10675
  have eq10898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10697 eq10672
    | exact resolve eq10672 eq10697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10672 eq10697
  have eq10904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10898
  have eq10906 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10904
       have r₂ := eq27
       grind)
    | exact resolve eq10904 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10904
  have eq10925 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10906 eq250
    | exact resolve eq250 eq10906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq10906
  have eq10990 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10925 eq101
    | exact resolve eq101 eq10925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq10925
  have eq11021 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq10990
    | exact resolve eq10990 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10990
  have eq11024 : x = (k y x) := by
    first
    | (have r₁ := eq11021
       have r₂ := eq50
       grind)
    | exact resolve eq11021 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq11021
  have eq11091 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq870 y x
       have i₂ := eq11024
       grind)
    | exact superpose eq11024 eq870
    | (have j0 := eq870 y x
       grind)
    | exact resolve eq870 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq11092 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq853 y x
       have i₂ := eq11024
       grind)
    | exact superpose eq11024 eq853
    | (have j0 := eq853 y x
       grind)
    | exact resolve eq853 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq11094 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq11024
       grind)
    | exact superpose eq11024 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11095 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq11094
  have eq11097 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11092
  have eq11098 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11091
  have eq11101 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11095
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11095
    | exact resolve eq11095 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11095
  have eq11103 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11097
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11097
    | exact resolve eq11097 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11097
  have eq11104 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11098
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11098
    | exact resolve eq11098 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11098
  have eq11115 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11103
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11103
    | exact resolve eq11103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11103
  have eq11116 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11104
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11104
    | exact resolve eq11104 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11104
  have eq11120 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq11115
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11115
    | exact resolve eq11115 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11115
  have eq11121 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11116
    | exact resolve eq11116 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11116
  have eq11124 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq11120
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11120
    | exact resolve eq11120 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11120
  have eq11125 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11121
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11121
    | exact resolve eq11121 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11121
  have eq11128 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11124
    | exact resolve eq11124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11124
  have eq11129 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11125
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11125
    | exact resolve eq11125 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11125
  have eq11131 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11129
    | exact resolve eq11129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11129
  have eq11167 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11131 eq27
    | exact resolve eq27 eq11131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11131
  have eq12229 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) x) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq11101
       grind)
    | exact superpose eq11101 eq14
    | exact resolve eq14 eq11101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12237 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq271 y x
       have i₂ := eq11101
       grind)
    | exact superpose eq11101 eq271
    | exact resolve eq271 eq11101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq11101
  have eq12250 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12237
       have i₂ := eq11024
       grind)
    | exact superpose eq11024 eq12237
    | exact resolve eq12237 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11024 eq12237
  have eq12254 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12250
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12250
    | exact resolve eq12250 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12250
  have eq12256 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12254
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12254
    | exact resolve eq12254 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12254
  have eq12257 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12256
  have eq12259 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12257 eq20
    | exact resolve eq20 eq12257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12257
  have eq12369 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12259
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12259
    | exact resolve eq12259 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12259
  have eq12537 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12369 eq26
    | exact resolve eq26 eq12369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12607 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12369 eq11167
    | (have r₁ := eq11167
       have r₂ := eq12369
       grind)
    | exact resolve eq11167 eq12369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12609 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12607
  have eq13296 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11128 eq14
    | exact resolve eq14 eq11128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11128
  have eq27759 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13296
    | (have j0 := eq13296 (σ y)
       grind)
    | exact resolve eq13296 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13296
  have eq27832 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12369 eq27759
    | exact resolve eq27759 eq12369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12369 eq27759
  have eq27891 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27832
       have r₂ := eq27
       grind)
    | exact resolve eq27832 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27832
  have eq27953 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12609 eq27891
    | exact resolve eq27891 eq12609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12609 eq27891
  have eq28004 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq27953
  have eq28062 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1014 eq28004
    | exact resolve eq28004 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq28004
  have eq28113 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq28062
  have eq28117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28113 eq12537
    | exact resolve eq12537 eq28113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12537 eq28113
  have eq28158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq28117
  have eq28160 : x = (M.op x y) := by
    first
    | (have r₁ := eq28158
       have r₂ := eq27
       grind)
    | exact resolve eq28158 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28158
  have eq28164 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28160 eq20
    | exact resolve eq20 eq28160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq28206 : x = (M.op x x) := by
    first
    | exact superpose eq28160 eq214
    | exact resolve eq214 eq28160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq28277 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28164
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28164
    | exact resolve eq28164 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28164
  have eq28483 : y = (M.op (M.op x x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12229 x
       have i₂ := eq28206
       grind)
    | exact superpose eq28206 eq12229
    | exact resolve eq12229 eq28206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12229
  have eq28533 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28483
       have i₂ := eq28206
       grind)
    | exact superpose eq28206 eq28483
    | exact resolve eq28483 eq28206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28206 eq28483
  have eq28542 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28533
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28533
    | exact resolve eq28533 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28533
  have eq28543 : y = (M.op x y) := by grind
  clear eq28542
  have eq28546 : x = y := by
    first
    | exact superpose eq28160 eq28543
    | exact resolve eq28543 eq28160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28160 eq28543
  have eq28552 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq28546
       grind)
    | exact superpose eq28546 eq24
    | exact resolve eq24 eq28546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28546
  have eq28696 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28552
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28552
    | exact resolve eq28552 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28552
  have eq28749 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28277 eq28696
    | exact resolve eq28696 eq28277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28696
  have eq28864 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28749 eq11167
    | (have r₁ := eq11167
       have r₂ := eq28749
       grind)
    | exact resolve eq11167 eq28749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11167 eq28749
  have eq28881 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28864
  have eq28895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28277 eq28881
    | exact resolve eq28881 eq28277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28277 eq28881
  have eq28978 : False := by grind
  exact eq28978
