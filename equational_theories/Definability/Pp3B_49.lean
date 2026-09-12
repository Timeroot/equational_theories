import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pyx_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq22
    | exact resolve eq22 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq38 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq46 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq24 (τ X0) (τ X0)
       grind)
    | exact superpose eq24 eq38
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq43
    | exact resolve eq43 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq26 X1 X2 X0
       grind)
    | exact superpose eq26 eq22
    | exact resolve eq22 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 y y
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq72
  have eq186 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq188 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq186
    | (have j0 := eq186 X0
       grind)
    | exact resolve eq186 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq521 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq70 X0 (τ X0)
       grind)
    | exact superpose eq70 eq46
    | (have j1 := eq70 X0 (τ X0)
       grind)
    | exact resolve eq46 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq534 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op X0 X0) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (M.op (τ X1) X0) X2
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq43
    | (have j1 := eq70 X1 X0
       grind)
    | exact resolve eq43 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq70
  have eq540 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq521 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq541 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op X0 X0) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq534 X0 X1 X2
       have i₂ := eq59 X0 X1 X2
       grind)
    | exact superpose eq59 eq534
    | (have j0 := eq534 X0 X1 X2
       grind)
    | exact resolve eq534 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq534
  have eq546 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq540 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq540
    | (have j0 := eq540 X0
       grind)
    | exact resolve eq540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq653 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) = (σ (k (τ (k X0 X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq188 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq188
    | (have j0 := eq188 (τ X0)
       grind)
    | exact resolve eq188 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq670 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) = (k (σ (τ (k X0 X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq653 X0
       have i₂ := eq19 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq19 eq653
    | (have j0 := eq653 X0
       grind)
    | exact resolve eq653 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq653
  have eq678 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (σ (τ X0)) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq670 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq670
    | (have j0 := eq670 X0
       grind)
    | exact resolve eq670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq683 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq678 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq678
    | (have j0 := eq678 X0
       grind)
    | exact resolve eq678 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq687 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq683 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq683
    | (have j0 := eq683 X0
       grind)
    | exact resolve eq683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq1266 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (k (σ X0) (σ X0)) X0
       have i₂ := eq546 (σ X0)
       grind)
    | exact superpose eq546 eq36
    | (have j1 := eq546 (σ X0)
       grind)
    | exact resolve eq36 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq1274 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1266 x
       have i₂ := eq36 (σ x) x
       grind)
    | exact superpose eq36 eq1266
    | (have j0 := eq1266 X0
       grind)
    | exact resolve eq1266 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq1290 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1274 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1274
    | (have j0 := eq1274 X0
       grind)
    | exact resolve eq1274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1304 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1290 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1290
    | (have j0 := eq1290 X0
       grind)
    | exact resolve eq1290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1336 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq687 X0
       have i₂ := eq1304 X0
       grind)
    | exact superpose eq1304 eq687
    | (have j0 := eq687 X0
       have j1 := eq1304 X0
       grind)
    | exact resolve eq687 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq1346 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1336 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1389 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq172
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq172
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq172 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq1390 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq1389
  have eq1400 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 (k X0 X0) X1
       have i₂ := eq1346 X0
       grind)
    | exact superpose eq1346 eq26
    | (have j1 := eq1346 X0
       grind)
    | exact resolve eq26 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1790 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X0 X0 X0
       have i₂ := eq1400 X0 X1
       grind)
    | exact superpose eq1400 eq98
    | (have j1 := eq1400 X0 X2
       grind)
    | exact resolve eq98 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1829 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1790 X0 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq1790
    | (have j0 := eq1790 X0 X1 X2
       grind)
    | exact resolve eq1790 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq2048 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1829 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq2049 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2048 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2125 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq2049 X0
       grind)
    | exact superpose eq2049 eq9
    | exact resolve eq9 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2127 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k X0 X0) X0 X0
       have i₂ := eq2049 X0
       grind)
    | exact superpose eq2049 eq23
    | exact resolve eq23 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2049
  have eq2174 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2127 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2127
    | exact resolve eq2127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2270 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2125 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2125
    | exact resolve eq2125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2337 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ (k X0 X0)) (σ X0) X1
       have i₂ := eq2174 X0
       grind)
    | exact superpose eq2174 eq26
    | exact resolve eq26 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq23440 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1304 (τ X0)
       have i₂ := eq541 (τ X0) X0 X0
       grind)
    | exact superpose eq541 eq1304
    | (have j0 := eq1304 (τ X0)
       have j1 := eq541 (τ X0) X0 x
       grind)
    | exact resolve eq1304 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq1304
  have eq23518 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq23440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23440
  have eq23573 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23518 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq23518
    | (have j0 := eq23518 X0
       grind)
    | exact resolve eq23518 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23518
  have eq23611 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq23573
  have eq23630 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23611 X0
       have i₂ := eq24 (τ X0) (τ X0)
       grind)
    | exact superpose eq24 eq23611
    | (have j0 := eq23611 X0
       grind)
    | exact resolve eq23611 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23611
  have eq24734 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq23630
  have eq24843 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24734 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq24734
    | (have j0 := eq24734 X0
       grind)
    | exact resolve eq24734 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq24734
  have eq24844 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq24843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24843
  have eq24854 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq24844 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24844
    | exact resolve eq24844 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24844
  have eq25026 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq24854 X0
       have i₂ := eq36 (σ X0) X0
       grind)
    | exact superpose eq36 eq24854
    | exact resolve eq24854 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq24854
  have eq25059 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq25026 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25026
    | exact resolve eq25026 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25026
  have eq25682 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2174 X0
       have i₂ := eq25059 X0
       grind)
    | exact superpose eq25059 eq2174
    | exact resolve eq2174 eq25059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq25688 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2270 X0
       have i₂ := eq25059 X0
       grind)
    | exact superpose eq25059 eq2270
    | exact resolve eq2270 eq25059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq25693 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2337 X0 X1
       have i₂ := eq25059 X0
       grind)
    | exact superpose eq25059 eq2337
    | exact resolve eq2337 eq25059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337
  have eq25774 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq25059 (σ X0)
       grind)
    | exact superpose eq25059 eq15
    | exact resolve eq15 eq25059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25835 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25774 X0
       have i₂ := eq25059 X0
       grind)
    | exact superpose eq25059 eq25774
    | exact resolve eq25774 eq25059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25059 eq25774
  have eq26795 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25682 y
       have i₂ := eq1390
       grind)
    | exact superpose eq1390 eq25682
    | exact resolve eq25682 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390 eq25682
  have eq26907 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq26795
  have eq26937 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26907
       have i₂ := eq25835 y
       grind)
    | exact superpose eq25835 eq26907
    | exact resolve eq26907 eq25835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26907
  have eq26957 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26937
       have i₂ := eq25835 x
       grind)
    | exact superpose eq25835 eq26937
    | exact resolve eq26937 eq25835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25835 eq26937
  have eq153823 : (M.op x x) = (τ (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq26957
       grind)
    | exact superpose eq26957 eq10
    | exact resolve eq10 eq26957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26957
  have eq154098 : y = (M.op x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153823
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq153823
    | exact resolve eq153823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153823
  have eq154099 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x x) := by grind
  clear eq154098
  have eq154215 : (M.op y y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq154099
       grind)
    | exact superpose eq154099 eq10
    | exact resolve eq10 eq154099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154099
  have eq154491 : y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq154215
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq154215
    | exact resolve eq154215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154215
  have eq155267 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq25688 x
       have i₂ := eq154491
       grind)
    | exact superpose eq154491 eq25688
    | exact resolve eq25688 eq154491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25688
  have eq155322 : y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq154491
       grind)
    | exact superpose eq154491 eq24
    | exact resolve eq24 eq154491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq154491
  have eq166354 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq155267
       grind)
    | exact superpose eq155267 eq16
    | exact resolve eq16 eq155267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155267
  have eq166576 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq166354
       have i₂ := eq155322
       grind)
    | exact superpose eq155322 eq166354
    | exact resolve eq166354 eq155322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155322 eq166354
  have eq166577 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by grind
  clear eq166576
  have eq166578 : y = (M.op y y) := by grind
  clear eq166577
  have eq167139 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25693 y X0
       have i₂ := eq166578
       grind)
    | exact superpose eq166578 eq25693
    | exact resolve eq25693 eq166578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25693
  have eq167195 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq98 X0 y y
       have i₂ := eq166578
       grind)
    | exact superpose eq166578 eq98
    | exact resolve eq98 eq166578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq166578
  have eq167395 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq167195 x
       have i₂ := eq22 y x
       grind)
    | exact superpose eq22 eq167195
    | exact resolve eq167195 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167195
  have eq167427 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq167139 X0
       have i₂ := eq22 (σ y) X0
       grind)
    | exact superpose eq22 eq167139
    | exact resolve eq167139 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167139
  have eq171651 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ y) X0
       have i₂ := eq167427 X0
       grind)
    | exact superpose eq167427 eq22
    | exact resolve eq22 eq167427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq167427
  have eq175609 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq171651 (σ x)
       grind)
    | exact superpose eq171651 eq16
    | exact resolve eq16 eq171651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171651
  have eq175750 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq175609
       have i₂ := eq167395 x
       grind)
    | exact superpose eq167395 eq175609
    | exact resolve eq175609 eq167395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167395 eq175609
  have eq175751 : False := by grind
  exact eq175751

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  clear eq19
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
  have eq75 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq403 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq489 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq403 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq403 X0 X1
       grind)
    | exact superpose eq403 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq403 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq403 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq403 X0 X1
       grind)
    | exact resolve eq13 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq500 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq489 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq501 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq500 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq506 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq501 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq501
    | (have j0 := eq501 X0 X1
       grind)
    | exact resolve eq501 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq507 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq506 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq897 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq507 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq507
    | (have j0 := eq507 (τ X1) (τ X0)
       grind)
    | exact resolve eq507 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq916 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq507 X0 X1
       grind)
    | exact superpose eq507 eq10
    | (have j1 := eq507 X0 X1
       grind)
    | exact resolve eq10 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq938 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq897 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq897
    | (have j0 := eq897 X0 X1
       grind)
    | exact resolve eq897 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq955 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq938 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq938
    | (have j0 := eq938 X0 X1
       grind)
    | exact resolve eq938 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq960 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq955
    | (have j0 := eq955 X0 X1
       grind)
    | exact resolve eq955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq965 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq960 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq960
    | (have j0 := eq960 X0 X1
       grind)
    | exact resolve eq960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq970 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq965 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq965
    | (have j0 := eq965 X0 X1
       grind)
    | exact resolve eq965 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq981 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq507 X0 X1
       have i₂ := eq970 X1 X0
       grind)
    | exact superpose eq970 eq507
    | (have j0 := eq507 X0 X1
       have j1 := eq970 (σ X1) (σ X0)
       grind)
    | exact resolve eq507 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq991 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq970 (σ X1) X0
       grind)
    | exact superpose eq970 eq29
    | (have j1 := eq970 (σ X1) X0
       grind)
    | exact resolve eq29 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) ∨ (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq991 (M.op (σ X0) X1) X0
       have i₂ := eq64 (σ X0) X1
       grind)
    | exact superpose eq64 eq991
    | (have j0 := eq991 (M.op (σ X0) X1) X0
       grind)
    | exact resolve eq991 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1049 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) ∨ (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1022 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1022
    | (have j0 := eq1022 X0 X1
       grind)
    | exact resolve eq1022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq15149 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) X1 X1
       have i₂ := eq1049 X0 X1
       grind)
    | exact superpose eq1049 eq68
    | (have j1 := eq1049 X0 X1
       grind)
    | exact resolve eq68 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq15172 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (M.op (σ X0) X1)) ∨ (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 (M.op (σ X0) X1)
       have i₂ := eq1049 X0 X1
       grind)
    | exact superpose eq1049 eq75
    | (have j1 := eq1049 X0 X1
       grind)
    | exact resolve eq75 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1049
  have eq15293 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op (σ (τ X0)) X1)))) ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ (M.op (σ (τ X0)) X1))
       have i₂ := eq15149 (τ X0) X1
       grind)
    | exact superpose eq15149 eq18
    | (have j1 := eq15149 (τ X0) X1
       grind)
    | exact resolve eq18 eq15149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15149
  have eq15312 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (M.op (σ (τ X0)) X1)) ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15293 X0 X1
       have i₂ := eq11 (M.op (σ (τ X0)) X1)
       grind)
    | exact superpose eq11 eq15293
    | (have j0 := eq15293 X0 X1
       grind)
    | exact resolve eq15293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15293
  have eq15348 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15312 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15312
    | (have j0 := eq15312 X0 X1
       grind)
    | exact resolve eq15312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15312
  have eq15371 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15348 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15348
    | (have j0 := eq15348 X0 X1
       grind)
    | exact resolve eq15348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15348
  have eq27150 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (M.op (σ X0) X1)) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq15371 eq15172
    | (have j0 := eq15172 X0 X1
       have j1 := eq15371 (σ X0) X1
       grind)
    | exact resolve eq15172 eq15371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15172 eq15371
  have eq27181 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op (σ X0) X1)
       have i₂ := eq27150 X0 X1
       grind)
    | exact superpose eq27150 eq29
    | (have j1 := eq27150 X0 X1
       grind)
    | exact resolve eq29 eq27150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27150
  have eq27212 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27181 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27181
    | (have j0 := eq27181 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq27181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27181
  have eq27446 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 ∨ (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27212 X0 (M.op (σ X0) X1)
       have i₂ := eq66 (σ X0) X1
       grind)
    | exact superpose eq66 eq27212
    | (have j0 := eq27212 X0 X1
       grind)
    | exact resolve eq27212 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27212
  have eq27513 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27446 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27446
  have eq27642 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27513 X1 (σ X0)
       have i₂ := eq916 X1 X0
       grind)
    | exact superpose eq916 eq27513
    | (have j1 := eq916 X1 X0
       grind)
    | exact resolve eq27513 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq27675 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op (σ (τ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ (M.op (σ (τ X0)) X1))
       have i₂ := eq27513 (τ X0) X1
       grind)
    | exact superpose eq27513 eq18
    | exact resolve eq18 eq27513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27694 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27675 X0 X1
       have i₂ := eq11 (M.op (σ (τ X0)) X1)
       grind)
    | exact superpose eq11 eq27675
    | exact resolve eq27675 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27675
  have eq27734 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27694 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27694
    | exact resolve eq27694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27694
  have eq27796 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27734 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq27734
    | exact resolve eq27734 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27950 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) X1) X0
       have i₂ := eq27796 (σ X0) X1
       grind)
    | exact superpose eq27796 eq23
    | exact resolve eq23 eq27796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27796
  have eq33177 : ∀ X0 X1 X2 : G, (k (M.op (σ X0) (σ X0)) (σ X2)) = (σ (k X1 X2)) ∨ (k X0 (k X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X2
       have i₂ := eq27642 X1 X0
       grind)
    | exact superpose eq27642 eq15
    | (have j1 := eq27642 X1 X0
       grind)
    | exact resolve eq15 eq27642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27642
  have eq266222 : ∀ X0 X1 X2 : G, (k X2 X1) = (τ (k (M.op (σ X0) (σ X0)) (σ X1))) ∨ (k X0 (k X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X2 X1)
       have i₂ := eq33177 X0 X2 X1
       grind)
    | exact superpose eq33177 eq10
    | (have j1 := eq33177 X0 X2 X2
       grind)
    | exact resolve eq10 eq33177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33177
  have eq266477 : ∀ X0 X1 X2 : G, (k (τ (M.op (σ X0) (σ X0))) X1) = (k X2 X1) ∨ (k X0 (k X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq266222 X0 X1 X2
       have i₂ := eq23 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq23 eq266222
    | (have j0 := eq266222 X0 X1 X2
       grind)
    | exact resolve eq266222 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq266222
  have eq266800 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 (k X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq266477 X0 X0 X1
       have i₂ := eq27950 X0 (σ X0)
       grind)
    | exact superpose eq27950 eq266477
    | (have j0 := eq266477 X0 X1 X1
       grind)
    | exact resolve eq266477 eq27950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27950 eq266477
  have eq269773 : ∀ X0 X1 : G, (k X1 (k X0 X1)) = X1 ∨ (k X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27513 X1 (σ X1)
       have i₂ := eq266800 X1 X0
       grind)
    | exact superpose eq266800 eq27513
    | (have j1 := eq266800 X1 X0
       grind)
    | exact resolve eq27513 eq266800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266800
  have eq269960 : ∀ X0 X1 : G, (k X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq269773 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269773
  have eq270770 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = X1 ∨ (M.op (k X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq269960 X0 X1
       have i₂ := eq970 X1 (k X0 X1)
       grind)
    | exact superpose eq970 eq269960
    | (have j1 := eq970 X1 (k X0 X1)
       grind)
    | exact resolve eq269960 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq277216 : ∀ X0 X1 : G, (M.op (k X1 X0) X0) = X0 ∨ (M.op (k X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66 (k X0 X1) (k X0 X1)
       have i₂ := eq270770 X0 X1
       grind)
    | exact superpose eq270770 eq66
    | (have j1 := eq270770 X1 X0
       grind)
    | exact resolve eq66 eq270770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq270770
  have eq277441 : ∀ X0 X1 : G, (M.op (k X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq277216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277216
  have eq277618 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq277441 (k X1 X0) X0
       have i₂ := eq269960 X1 X0
       grind)
    | exact superpose eq269960 eq277441
    | exact resolve eq277441 eq269960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269960
  have eq277630 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq277441 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq277441
    | exact resolve eq277441 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277441
  have eq279400 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq277630 X0 (M.op X0 X1)
       have i₂ := eq27734 X0 X1
       grind)
    | exact superpose eq27734 eq277630
    | exact resolve eq277630 eq27734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277630
  have eq312808 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq981 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq312858 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq312808 x y
       grind)
    | exact superpose eq312808 eq16
    | (have j1 := eq312808 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq312808 x y
       grind)
    | exact resolve eq16 eq312808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312808
  have eq313179 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq312858
  have eq313277 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq27513 x (σ x)
       have i₂ := eq313179
       grind)
    | exact superpose eq313179 eq27513
    | exact resolve eq27513 eq313179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27513 eq313179
  have eq313610 : y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq313277
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq313277
    | exact resolve eq313277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313277
  have eq313776 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq27734 x x
       have i₂ := eq313610
       grind)
    | exact superpose eq313610 eq27734
    | exact resolve eq27734 eq313610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27734 eq313610
  have eq313913 : x = (k x y) := by grind
  clear eq313776
  have eq314153 : x = (M.op y x) := by
    first
    | (have i₁ := eq277618 y x
       have i₂ := eq313913
       grind)
    | exact superpose eq313913 eq277618
    | exact resolve eq277618 eq313913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277618 eq313913
  have eq314180 : x = (M.op y x) := by grind
  clear eq314153
  have eq317482 : y = (M.op x y) := by
    first
    | (have i₁ := eq64 y x
       have i₂ := eq314180
       grind)
    | exact superpose eq314180 eq64
    | exact resolve eq64 eq314180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq314180
  have eq317725 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq317482
       grind)
    | exact superpose eq317482 eq16
    | exact resolve eq16 eq317482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317978 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq279400 x y
       have i₂ := eq317482
       grind)
    | exact superpose eq317482 eq279400
    | exact resolve eq279400 eq317482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279400 eq317482
  have eq317993 : False := by grind
  exact eq317993

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
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
  have eq75 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq76 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq77 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq66 (σ X0) (σ X0)
       grind)
    | exact superpose eq66 eq76
    | exact resolve eq76 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq66 (τ X0) (τ X0)
       grind)
    | exact superpose eq66 eq75
    | exact resolve eq75 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq84 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq68 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X3
       have i₂ := eq68 X1 X2 X0
       grind)
    | exact superpose eq68 eq68
    | exact resolve eq68 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
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
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op X1 X0) (M.op X1 X2))) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq68 X1 X2 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op X2 X3))) X4) X0) X5) X4) X5) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq84 X4 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op X2 X3))) X0 X5
       have i₂ := eq91 X1 X2 X3 X0
       grind)
    | exact superpose eq91 eq84
    | exact resolve eq84 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq91
  have eq591 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq596 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq779 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq591 x y
       grind)
    | exact superpose eq591 eq16
    | (have j1 := eq591 x y
       grind)
    | exact resolve eq16 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 x
       have i₂ := eq591 x x
       grind)
    | exact superpose eq591 eq77
    | (have j1 := eq591 X0 X0
       grind)
    | exact resolve eq77 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq591
  have eq806 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq802 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq809 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq780 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq810 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq806 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq806
    | (have j0 := eq806 X0
       grind)
    | exact resolve eq806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq813 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq809 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq809
    | (have j0 := eq809 X0
       grind)
    | exact resolve eq809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq874 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq813 (σ X0)
       grind)
    | exact superpose eq813 eq23
    | (have j1 := eq813 (σ X0)
       grind)
    | exact resolve eq23 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq882 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq874 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq874
    | (have j0 := eq874 X0
       grind)
    | exact resolve eq874 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq898 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq882 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq882
    | (have j0 := eq882 X0
       grind)
    | exact resolve eq882 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq4975 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq898 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq898
    | (have j0 := eq898 (τ X0)
       grind)
    | exact resolve eq898 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq5055 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq4975 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq4975
    | (have j0 := eq4975 X0
       grind)
    | exact resolve eq4975 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4975
  have eq5095 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5055 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5055
    | (have j0 := eq5055 X0
       grind)
    | exact resolve eq5055 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5055
  have eq5189 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq5095 X0
       grind)
    | exact superpose eq5095 eq77
    | (have j1 := eq5095 X0
       grind)
    | exact resolve eq77 eq5095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq5196 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) (σ X0) X1
       have i₂ := eq5095 X0
       grind)
    | exact superpose eq5095 eq68
    | (have j1 := eq5095 X0
       grind)
    | exact resolve eq68 eq5095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5095
  have eq5245 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5196 X0 X1
       have i₂ := eq64 (σ X0) X1
       grind)
    | exact superpose eq64 eq5196
    | (have j0 := eq5196 X0 X1
       grind)
    | exact resolve eq5196 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5196
  have eq5249 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5189 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5189
    | (have j0 := eq5189 X0
       grind)
    | exact resolve eq5189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5189
  have eq5300 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (τ (k (σ X0) (σ X0))) = (τ (k (k (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq5249 (σ X0)
       grind)
    | exact superpose eq5249 eq29
    | (have j1 := eq5249 (σ X0)
       grind)
    | exact resolve eq29 eq5249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5249
  have eq5356 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (k (σ X0) (σ X0))) = (τ (k (k (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5300 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5300
    | (have j0 := eq5300 X0
       grind)
    | exact resolve eq5300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5300
  have eq5411 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5356 X0
       have i₂ := eq23 (k (σ X0) (σ X0)) X0
       grind)
    | exact superpose eq23 eq5356
    | (have j0 := eq5356 X0
       grind)
    | exact resolve eq5356 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5356
  have eq5463 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5411 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq5411
    | (have j0 := eq5411 X0
       grind)
    | exact resolve eq5411 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5411
  have eq5513 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5463 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5463
    | (have j0 := eq5463 X0
       grind)
    | exact resolve eq5463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463
  have eq5581 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5513 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq5513
    | exact resolve eq5513 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5513
  have eq5661 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5581 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq5581
    | (have j0 := eq5581 X0
       grind)
    | exact resolve eq5581 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5581
  have eq6293 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (τ (k (τ X0) (τ X0))) = (τ (k (k (τ X0) (τ X0)) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5245 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5245
    | (have j0 := eq5245 (τ X0) X1
       grind)
    | exact resolve eq5245 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5245
  have eq6359 : ∀ X0 X1 : G, (τ (τ (k X0 X0))) = (τ (k (τ (k X0 X0)) (τ X0))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6293 X0 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq6293
    | (have j0 := eq6293 X0 X1
       grind)
    | exact resolve eq6293 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6293
  have eq6360 : ∀ X0 X1 : G, (τ (τ (k X0 X0))) = (τ (τ (k (k X0 X0) X0))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6359 X0 X1
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq6359
    | (have j0 := eq6359 X0 X1
       grind)
    | exact resolve eq6359 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6359
  have eq7773 : ∀ X0 X1 : G, (τ (k (k X0 X0) X0)) = (σ (τ (τ (k X0 X0)))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (τ (k (k X0 X0) X0))
       have i₂ := eq6360 X0 X1
       grind)
    | exact superpose eq6360 eq11
    | (have j1 := eq6360 X0 X1
       grind)
    | exact resolve eq11 eq6360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6360
  have eq7880 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7773 X0 X1
       have i₂ := eq11 (τ (k X0 X0))
       grind)
    | exact superpose eq11 eq7773
    | (have j0 := eq7773 X0 X1
       grind)
    | exact resolve eq7773 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7773
  have eq7922 : ∀ X0 X1 : G, (k (k X0 X0) X0) = (σ (τ (k X0 X0))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (k X0 X0) X0)
       have i₂ := eq7880 X0 X1
       grind)
    | exact superpose eq7880 eq11
    | (have j1 := eq7880 X0 X1
       grind)
    | exact resolve eq11 eq7880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7880
  have eq8029 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7922 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq7922
    | (have j0 := eq7922 X0 X1
       grind)
    | exact resolve eq7922 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7922
  have eq8091 : ∀ X0 X1 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq8029 (τ X0) X1
       grind)
    | exact superpose eq8029 eq19
    | (have j1 := eq8029 (τ X0) X1
       grind)
    | exact resolve eq19 eq8029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8029
  have eq8129 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8091 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq8091
    | (have j0 := eq8091 X0 X1
       grind)
    | exact resolve eq8091 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8091
  have eq8169 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8129 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8129
    | (have j0 := eq8129 X0 X1
       grind)
    | exact resolve eq8129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8129
  have eq8488 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    grind
  clear eq8169
  have eq8489 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8488 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq8488
    | (have j0 := eq8488 X0
       grind)
    | exact resolve eq8488 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8488
  have eq8499 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq8582 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8499 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8499
    | (have j0 := eq8499 X0 X1
       grind)
    | exact resolve eq8499 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8499
  have eq12447 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq78 X0
       have i₂ := eq8489 X0
       grind)
    | exact superpose eq8489 eq78
    | (have j1 := eq8489 X0
       grind)
    | exact resolve eq78 eq8489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq8489
  have eq12500 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12447 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq12447
    | (have j0 := eq12447 X0
       grind)
    | exact resolve eq12447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12447
  have eq12501 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12500 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12500
  have eq12983 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq810 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq810
    | exact resolve eq810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq13101 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12983 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq12983
    | (have j0 := eq12983 X0
       grind)
    | exact resolve eq12983 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12983
  have eq13128 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (σ (k (k (τ X0) (τ X0)) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13101 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13101
    | (have j0 := eq13101 X0
       grind)
    | exact resolve eq13101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101
  have eq13135 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13128 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq13128
    | (have j0 := eq13128 X0
       grind)
    | exact resolve eq13128 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13128
  have eq13140 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13135 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq13135
    | (have j0 := eq13135 X0
       grind)
    | exact resolve eq13135 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq13135
  have eq13144 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13140 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13140
    | (have j0 := eq13140 X0
       grind)
    | exact resolve eq13140 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13140
  have eq13145 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13144 X0
       have i₂ := eq12501 X0
       grind)
    | exact superpose eq12501 eq13144
    | (have j0 := eq13144 X0
       grind)
    | exact resolve eq13144 eq12501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13144
  have eq13157 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 (k X0 X0) X1
       have i₂ := eq13145 X0
       grind)
    | exact superpose eq13145 eq68
    | (have j1 := eq13145 X0
       grind)
    | exact resolve eq68 eq13145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13145
  have eq13343 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 X0 X0 X0
       have i₂ := eq13157 X0 X1
       grind)
    | exact superpose eq13157 eq90
    | (have j1 := eq13157 X0 X2
       grind)
    | exact resolve eq90 eq13157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13157
  have eq13413 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13343 X0 X1 X2
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq13343
    | (have j0 := eq13343 X0 X1 X2
       grind)
    | exact resolve eq13343 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13343
  have eq13778 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13413 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13413
  have eq13779 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13778 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13778
  have eq13822 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq13779 X0
       grind)
    | exact superpose eq13779 eq9
    | exact resolve eq9 eq13779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13824 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 (k X0 X0) X0 X0
       have i₂ := eq13779 X0
       grind)
    | exact superpose eq13779 eq65
    | exact resolve eq65 eq13779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq13779
  have eq13892 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13824 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq13824
    | exact resolve eq13824 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13893 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq13824 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq13824
    | exact resolve eq13824 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13824
  have eq13943 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13822 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq13822
    | exact resolve eq13822 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13822
  have eq14072 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ (k X0 X0)) (σ X0) X1
       have i₂ := eq13892 X0
       grind)
    | exact superpose eq13892 eq68
    | exact resolve eq68 eq13892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13892
  have eq14200 : ∀ X0 X1 : G, (M.op (M.op (τ (k X0 X0)) X1) (τ X0)) = (M.op X1 (M.op (M.op (τ (k X0 X0)) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (τ (k X0 X0)) (τ X0)
       have i₂ := eq13893 X0
       grind)
    | exact superpose eq13893 eq90
    | exact resolve eq90 eq13893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13893
  have eq46074 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq779
       have i₂ := eq8582 y x
       grind)
    | exact superpose eq8582 eq779
    | (have j1 := eq8582 (σ y) (σ x)
       grind)
    | (have r₁ := eq779
       have r₂ := eq8582 y x
       grind)
    | exact resolve eq779 eq8582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq8582
  have eq46075 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq46074
  have eq87517 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq596 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq596
    | exact resolve eq596 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq88103 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87517 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq87517
    | (have j0 := eq87517 X0 X1
       grind)
    | exact resolve eq87517 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq87517
  have eq88303 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5661 x
       have i₂ := eq88103 x x
       grind)
    | exact superpose eq88103 eq5661
    | (have j1 := eq88103 X0 X0
       grind)
    | exact resolve eq5661 eq88103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5661 eq88103
  have eq88581 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq88303 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88303
  have eq88656 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq88581 X0
       have i₂ := eq12501 X0
       grind)
    | exact superpose eq12501 eq88581
    | (have j0 := eq88581 X0
       grind)
    | exact resolve eq88581 eq12501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12501 eq88581
  have eq88801 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq88656 X0
       grind)
    | exact superpose eq88656 eq11
    | (have j1 := eq88656 X0
       grind)
    | exact resolve eq11 eq88656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88656
  have eq89005 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq88801 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88801
    | (have j0 := eq88801 X0
       grind)
    | exact resolve eq88801 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88801
  have eq89006 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq89005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89005
  have eq89117 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq89006 X0
       grind)
    | exact superpose eq89006 eq11
    | (have j1 := eq89006 X0
       grind)
    | exact resolve eq11 eq89006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89006
  have eq89304 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq89117 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq89117
    | (have j0 := eq89117 X0
       grind)
    | exact resolve eq89117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89117
  have eq89359 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq89304
  have eq89658 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq89359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89359
  have eq89895 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13943 X0
       have i₂ := eq89658 X0
       grind)
    | exact superpose eq89658 eq13943
    | exact resolve eq13943 eq89658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13943
  have eq89901 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14072 X0 X1
       have i₂ := eq89658 X0
       grind)
    | exact superpose eq89658 eq14072
    | exact resolve eq14072 eq89658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14072
  have eq89921 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) = (M.op X1 (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14200 X0 X1
       have i₂ := eq89658 X0
       grind)
    | exact superpose eq89658 eq14200
    | exact resolve eq14200 eq89658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14200
  have eq90016 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq89658 (σ X0)
       grind)
    | exact superpose eq89658 eq15
    | exact resolve eq15 eq89658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90016 X0
       have i₂ := eq89658 X0
       grind)
    | exact superpose eq89658 eq90016
    | exact resolve eq90016 eq89658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89658 eq90016
  have eq1873920 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 x y
       have i₂ := eq46075
       grind)
    | exact superpose eq46075 eq66
    | exact resolve eq66 eq46075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46075
  have eq1874974 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1873920
       have i₂ := eq90107 x
       grind)
    | exact superpose eq90107 eq1873920
    | exact resolve eq1873920 eq90107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90107 eq1873920
  have eq1875810 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq68 (σ x) (σ y) X0
       have i₂ := eq1874974
       grind)
    | exact superpose eq1874974 eq68
    | exact resolve eq68 eq1874974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1874974
  have eq1876854 : ∀ X0 : G, (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1875810 X0
       have i₂ := eq64 (σ x) X0
       grind)
    | exact superpose eq64 eq1875810
    | exact resolve eq1875810 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875810
  have eq1877471 : ∀ X0 : G, (M.op x x) = (τ (σ y)) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1876854 X0
       grind)
    | exact superpose eq1876854 eq10
    | (have j1 := eq1876854 X0
       grind)
    | exact resolve eq10 eq1876854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876854
  have eq1878291 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1877471 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1877471
    | (have j0 := eq1877471 X0
       grind)
    | exact resolve eq1877471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877471
  have eq1878292 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1878291 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878291
  have eq1878430 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89895 x
       have i₂ := eq1878292 X0
       grind)
    | exact superpose eq1878292 eq89895
    | (have j1 := eq1878292 (σ y)
       grind)
    | exact resolve eq89895 eq1878292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89895
  have eq1878916 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 x x
       have i₂ := eq1878292 X0
       grind)
    | exact superpose eq1878292 eq66
    | (have j1 := eq1878292 X0
       grind)
    | exact resolve eq66 eq1878292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1878292
  have eq1885133 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j0 := eq1878430 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878430
  have eq1885134 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1885133
  have eq1885207 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1885134
       grind)
    | exact superpose eq1885134 eq16
    | exact resolve eq16 eq1885134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885134
  have eq1885910 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1885207
       have i₂ := eq1878916 X0
       grind)
    | exact superpose eq1878916 eq1885207
    | (have j1 := eq1878916 X0
       grind)
    | exact resolve eq1885207 eq1878916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878916 eq1885207
  have eq1885912 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1885910 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885910
  have eq1885913 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1885912 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885912
  have eq1886429 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op X0 (M.op (M.op x X0) x)) ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 x x
       have i₂ := eq1885913 X0
       grind)
    | exact superpose eq1885913 eq90
    | (have j1 := eq1885913 X1
       grind)
    | exact resolve eq90 eq1885913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1885913
  have eq1887018 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1886429 X1 X1
       have i₂ := eq64 x X1
       grind)
    | exact superpose eq64 eq1886429
    | (have j0 := eq1886429 X0 X1
       grind)
    | exact resolve eq1886429 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886429
  have eq1887505 : ∀ X0 X1 : G, (M.op (M.op (τ (σ x)) X0) (τ (σ x))) = (M.op X0 (M.op (M.op (τ (σ x)) X0) (τ (σ x)))) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq89921 (σ x) X1
       have i₂ := eq1887018 X0 (σ x)
       grind)
    | exact superpose eq1887018 eq89921
    | (have j1 := eq1887018 X1 X1
       grind)
    | exact resolve eq89921 eq1887018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89921 eq1887018
  have eq1888772 : ∀ X0 X1 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1887505 X1 X1
       have i₂ := eq64 (τ (σ x)) X1
       grind)
    | exact superpose eq64 eq1887505
    | (have j0 := eq1887505 X0 X1
       grind)
    | exact resolve eq1887505 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887505
  have eq1888957 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1888772 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1888772
    | (have j0 := eq1888772 X0 X0
       grind)
    | exact resolve eq1888772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888772
  have eq1892753 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1888957 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888957
  have eq1892754 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1892753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892753
  have eq1892797 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89901 x X0
       have i₂ := eq1892754 x
       grind)
    | exact superpose eq1892754 eq89901
    | exact resolve eq89901 eq1892754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89901
  have eq1894682 : ∀ X4 : G, (M.op x X4) = X4 := by
    intro X4
    first
    | (have i₁ := eq563 x x x x x X4
       have i₂ := eq1892754 (M.op (M.op (M.op (M.op (M.op x x) (M.op (M.op x x) (M.op x x))) x) x) X4)
       grind)
    | exact superpose eq1892754 eq563
    | exact resolve eq563 eq1892754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq1892754
  have eq1895880 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1892797 X0
       have i₂ := eq64 (σ x) X0
       grind)
    | exact superpose eq64 eq1892797
    | exact resolve eq1892797 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1892797
  have eq1899422 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1895880 (σ y)
       grind)
    | exact superpose eq1895880 eq16
    | exact resolve eq16 eq1895880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895880
  have eq1900827 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1899422
       have i₂ := eq1894682 y
       grind)
    | (have i₁ := eq1899422
       have i₂ := eq1894682 (M.op x y)
       grind)
    | exact superpose eq1894682 eq1899422
    | exact resolve eq1899422 eq1894682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894682 eq1899422
  have eq1900828 : False := by grind
  exact eq1900828

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (M.op X0 X1) X0
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq66
    | exact resolve eq66 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq70 X1 X2 X0
       grind)
    | exact superpose eq70 eq66
    | exact resolve eq66 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq19
    | exact resolve eq19 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq384 : ∀ X0 : G, (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) = (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq23
    | exact resolve eq23 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq536 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq644 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq528 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq528
    | (have j0 := eq528 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq528 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq670 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq528 X1 X0
       grind)
    | exact superpose eq528 eq15
    | (have j1 := eq528 X1 X0
       grind)
    | exact resolve eq15 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq3934 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq551 (M.op (τ X1) X1) X1
       have i₂ := eq66 (τ X1) X1
       grind)
    | exact superpose eq66 eq551
    | (have j0 := eq551 (M.op (τ X0) X1) X0
       grind)
    | exact resolve eq551 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3936 : ∀ X0 : G, (σ (k (τ X0) (σ (τ (τ X0))))) = (k (σ (k (τ X0) (σ (τ (τ X0))))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq164 X0
       have i₂ := eq551 (τ (τ X0)) (τ X0)
       grind)
    | exact superpose eq551 eq164
    | (have j1 := eq551 (τ (τ X0)) (τ X0)
       grind)
    | exact resolve eq164 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq551
  have eq3992 : ∀ X0 : G, (σ (k (τ X0) (σ (τ (τ X0))))) = (k (σ (k (τ X0) (σ (τ (τ X0))))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq3936 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq3995 : ∀ X0 : G, (k X0 (σ (σ (τ (τ X0))))) = (k (k X0 (σ (σ (τ (τ X0))))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3992 X0
       have i₂ := eq18 X0 (σ (τ (τ X0)))
       grind)
    | exact superpose eq18 eq3992
    | (have j0 := eq3992 X0
       grind)
    | exact resolve eq3992 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3992
  have eq3997 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3934 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3934
    | (have j0 := eq3934 X0 X1
       grind)
    | exact resolve eq3934 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3934
  have eq4013 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3995 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq3995
    | (have j0 := eq3995 X0
       grind)
    | exact resolve eq3995 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3995
  have eq4014 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4013 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4013
    | (have j0 := eq4013 X0
       grind)
    | exact resolve eq4013 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4013
  have eq4591 : ∀ X0 X1 : G, (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) = (M.op X1 (M.op (M.op (τ (τ X0)) X1) (τ (τ X0)))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (τ (τ X0)) (τ (τ X0))
       have i₂ := eq4014 X0
       grind)
    | exact superpose eq4014 eq88
    | (have j1 := eq4014 X0
       grind)
    | exact resolve eq88 eq4014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq4014
  have eq4629 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4591 X0 X1
       have i₂ := eq66 (τ (τ X0)) X1
       grind)
    | exact superpose eq66 eq4591
    | (have j0 := eq4591 X0 X1
       grind)
    | exact resolve eq4591 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4591
  have eq6384 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq4629 (σ X0) X1
       grind)
    | exact superpose eq4629 eq23
    | (have j1 := eq4629 (σ X0) X1
       grind)
    | exact resolve eq23 eq4629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4629
  have eq6432 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6384 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6384
    | (have j0 := eq6384 X0 X1
       grind)
    | exact resolve eq6384 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6384
  have eq6472 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6432 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6432
    | (have j0 := eq6432 X0 X1
       grind)
    | exact resolve eq6432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6432
  have eq6508 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6472 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6472
    | (have j0 := eq6472 X0 X1
       grind)
    | exact resolve eq6472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6472
  have eq6582 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq6508 (σ X0) X1
       grind)
    | exact superpose eq6508 eq23
    | (have j1 := eq6508 (σ X0) X1
       grind)
    | exact resolve eq23 eq6508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6508
  have eq6630 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6582 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6582
    | (have j0 := eq6582 X0 X1
       grind)
    | exact resolve eq6582 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6582
  have eq6670 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6630 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6630
    | (have j0 := eq6630 X0 X1
       grind)
    | exact resolve eq6630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6630
  have eq6706 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6670 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6670
    | (have j0 := eq6670 X0 X1
       grind)
    | exact resolve eq6670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6670
  have eq6780 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq6706 (σ X0) X1
       grind)
    | exact superpose eq6706 eq23
    | (have j1 := eq6706 (σ X0) X1
       grind)
    | exact resolve eq23 eq6706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6706
  have eq6828 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6780 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6780
    | (have j0 := eq6780 X0 X1
       grind)
    | exact resolve eq6780 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6780
  have eq6868 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6828 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6828
    | (have j0 := eq6828 X0 X1
       grind)
    | exact resolve eq6828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6828
  have eq18134 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq670
  have eq18151 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18134
  have eq18167 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq6868 eq18151
    | (have j0 := eq18151 X0
       have j1 := eq6868 X0 (σ X0)
       grind)
    | exact resolve eq18151 eq6868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6868 eq18151
  have eq18195 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18167 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq18167
    | (have j0 := eq18167 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq18167 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18213 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq18167 (τ X0)
       grind)
    | exact superpose eq18167 eq19
    | (have j1 := eq18167 (τ X0)
       grind)
    | exact resolve eq19 eq18167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq18167
  have eq18284 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq18195 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18195
  have eq18289 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18213 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18213
    | (have j0 := eq18213 X0
       grind)
    | exact resolve eq18213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18213
  have eq18310 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18289 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18289
    | (have j0 := eq18289 X0
       grind)
    | exact resolve eq18289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18289
  have eq18339 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18310 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq18310
    | (have j0 := eq18310 (τ X0)
       grind)
    | exact resolve eq18310 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq18689 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq18339 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20826 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0) (σ X0)
       have i₂ := eq18284 X0
       grind)
    | exact superpose eq18284 eq68
    | (have j1 := eq18284 X0
       grind)
    | exact resolve eq68 eq18284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18284
  have eq20973 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq645 X0
       grind)
    | exact superpose eq645 eq66
    | (have j1 := eq645 X0
       grind)
    | exact resolve eq66 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21060 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq645 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23172 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq644 x y
       grind)
    | exact superpose eq644 eq16
    | (have j1 := eq644 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq644 x y
       grind)
    | exact resolve eq16 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq23288 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq23172
  have eq64559 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23288
       grind)
    | exact superpose eq23288 eq36
    | exact resolve eq36 eq23288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64572 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq64588 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68 (σ x) (σ x)
       have i₂ := eq23288
       grind)
    | exact superpose eq23288 eq68
    | exact resolve eq68 eq23288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23288
  have eq64700 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64572
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq64572
    | exact resolve eq64572 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64572
  have eq64711 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64559
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq64559
    | exact resolve eq64559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64559
  have eq64716 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq64700
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq64700 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64700
  have eq64719 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq64711
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq64711 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64711
  have eq64734 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq70 (σ x) (σ y) X0
       have i₂ := eq64719
       grind)
    | exact superpose eq64719 eq70
    | exact resolve eq70 eq64719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64719
  have eq64926 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq64734 X0
       have i₂ := eq66 (σ x) X0
       grind)
    | exact superpose eq66 eq64734
    | exact resolve eq64734 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64734
  have eq64959 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq64926 (σ x)
       grind)
    | exact superpose eq64926 eq36
    | exact resolve eq36 eq64926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65106 : y = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64959
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64959
    | exact resolve eq64959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64959
  have eq65233 : y = (M.op x x) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq66 x y
       have i₂ := eq65106
       grind)
    | exact superpose eq65106 eq66
    | exact resolve eq66 eq65106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65106
  have eq67170 : x = (M.op y x) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq66 x x
       have i₂ := eq65233
       grind)
    | exact superpose eq65233 eq66
    | exact resolve eq66 eq65233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65233
  have eq67272 : x = (k x x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq67170
  have eq67347 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq67272
       grind)
    | exact superpose eq67272 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq67272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67272
  have eq67348 : x = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq67347
  have eq67382 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66 y x
       have i₂ := eq67348
       grind)
    | exact superpose eq67348 eq66
    | exact resolve eq66 eq67348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67348
  have eq67488 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq67382 eq64926
    | (have j0 := eq64926 X0
       grind)
    | exact resolve eq64926 eq67382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64926
  have eq67597 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  have eq69183 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq66 (σ x) X0
       have i₂ := eq67488 X0
       grind)
    | exact superpose eq67488 eq66
    | exact resolve eq66 eq67488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67488
  have eq120545 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64588
       grind)
    | exact superpose eq64588 eq16
    | exact resolve eq16 eq64588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64588
  have eq120704 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq120545
       have r₂ := eq64716
       grind)
    | exact resolve eq120545 eq64716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64716 eq120545
  have eq120711 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq120704
       grind)
    | exact superpose eq120704 eq16
    | exact resolve eq16 eq120704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120721 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq70 (σ x) (σ y) X0
       have i₂ := eq120704
       grind)
    | exact superpose eq120704 eq70
    | exact resolve eq70 eq120704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120976 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq120721 X0
       have i₂ := eq66 (σ x) X0
       grind)
    | exact superpose eq66 eq120721
    | exact resolve eq120721 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120721
  have eq121005 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120704
       have i₂ := eq120976 (σ y)
       grind)
    | exact superpose eq120976 eq120704
    | exact resolve eq120704 eq120976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120704
  have eq121007 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq120976 (σ x)
       grind)
    | exact superpose eq120976 eq36
    | exact resolve eq36 eq120976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq121163 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq121005
  have eq121191 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq121007
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq121007
    | exact resolve eq121007 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121007
  have eq121391 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq121191
  have eq121549 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq68 x x
       have i₂ := eq121391
       grind)
    | exact superpose eq121391 eq68
    | exact resolve eq68 eq121391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121391
  have eq121866 : x ≠ y ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq121549
  have eq122433 : (σ x) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120711
       have i₂ := eq67382
       grind)
    | exact superpose eq67382 eq120711
    | exact resolve eq120711 eq67382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67382 eq120711
  have eq122435 : x = y ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122433
       have r₂ := eq121163
       grind)
    | exact resolve eq122433 eq121163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121163 eq122433
  have eq122436 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122435
       have r₂ := eq67597
       grind)
    | exact resolve eq122435 eq67597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122435
  have eq122455 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20826 x
       have i₂ := eq122436
       grind)
    | exact superpose eq122436 eq20826
    | (have j0 := eq20826 x
       grind)
    | exact resolve eq20826 eq122436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20826 eq122436
  have eq122615 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122455
       have r₂ := eq67597
       grind)
    | exact resolve eq122455 eq67597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67597 eq122455
  have eq122637 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq120976 eq122615
    | (have j1 := eq120976 (σ y)
       grind)
    | exact resolve eq122615 eq120976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120976 eq122615
  have eq124716 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (τ X0) X1 X1
       have i₂ := eq3997 X0 X1
       grind)
    | exact superpose eq3997 eq70
    | (have j1 := eq3997 X0 X1
       grind)
    | exact resolve eq70 eq3997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3997
  have eq129542 : ∀ X0 : G, (k X0 (σ (τ (k X0 X0)))) = X0 ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq124716 X0 (τ X0)
       have i₂ := eq18339 X0
       grind)
    | exact superpose eq18339 eq124716
    | (have j0 := eq124716 X0 (τ X0)
       have j1 := eq18339 X0
       grind)
    | exact resolve eq124716 eq18339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18339 eq124716
  have eq129676 : ∀ X0 : G, (k X0 (σ (τ (k X0 X0)))) = X0 ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq129542 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129542
  have eq129783 : ∀ X0 : G, (k X0 (σ (τ (k X0 X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq129676 X0
       have j1 := eq18689 X0
       grind)
    | (have r₁ := eq129676 X0
       have r₂ := eq18689 X0
       grind)
    | exact resolve eq129676 eq18689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18689 eq129676
  have eq129876 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq129783 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq129783
    | (have j0 := eq129783 X0
       grind)
    | exact resolve eq129783 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129783
  have eq130148 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21060 (τ X0)
       have i₂ := eq129876 X0
       grind)
    | exact superpose eq129876 eq21060
    | (have j1 := eq129876 X0
       grind)
    | exact resolve eq21060 eq129876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129876
  have eq130289 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq130148 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130148
  have eq130290 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq130289 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130289
  have eq130340 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq130290 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq130290
    | (have j0 := eq130290 X0
       grind)
    | exact resolve eq130290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130290
  have eq130360 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq18310 eq130340
    | (have j0 := eq130340 X0
       have j1 := eq18310 X0
       grind)
    | exact resolve eq130340 eq18310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18310 eq130340
  have eq152121 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq536 (M.op X0 X0) (σ X0)
       have i₂ := eq20973 X0
       grind)
    | exact superpose eq20973 eq536
    | (have j0 := eq536 X0 (σ (M.op X0 X0))
       have j1 := eq20973 X0
       grind)
    | exact resolve eq536 eq20973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq20973
  have eq152309 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq152121 X0
       have j1 := eq21060 X0
       grind)
    | (have r₁ := eq152121 X0
       have r₂ := eq21060 X0
       grind)
    | exact resolve eq152121 eq21060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21060 eq152121
  have eq152336 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq152309 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq152309
    | (have j0 := eq152309 X0
       grind)
    | exact resolve eq152309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152309
  have eq152347 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq130360 eq152336
    | (have j0 := eq152336 X0
       have j1 := eq130360 X0
       grind)
    | exact resolve eq152336 eq130360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152336
  have eq152354 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq130360 eq152347
    | (have j0 := eq152347 X0
       have j1 := eq130360 X0
       grind)
    | exact resolve eq152347 eq130360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152347
  have eq152355 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq152354 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152354
  have eq152362 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq130360 eq152355
    | (have j0 := eq152355 X0
       have j1 := eq130360 X0
       grind)
    | exact resolve eq152355 eq130360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130360 eq152355
  have eq152363 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq152362 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152362
  have eq152415 : ∀ X0 : G, (τ (τ (σ (σ X0)))) = (k (τ (τ (σ (σ X0)))) X0) ∨ (σ X0) = (k (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq384 X0
       have i₂ := eq152363 (σ X0)
       grind)
    | exact superpose eq152363 eq384
    | (have j1 := eq152363 (σ X0)
       grind)
    | exact resolve eq384 eq152363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq152363
  have eq152617 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq152415 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq152415
    | (have j0 := eq152415 X0
       grind)
    | exact resolve eq152415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152415
  have eq152628 : ∀ X0 : G, (σ X0) = (k (σ X0) (M.op (σ X0) (σ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq152617 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq152617
    | (have j0 := eq152617 X0
       grind)
    | exact resolve eq152617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152617
  have eq154958 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq152628 X0
       grind)
    | exact superpose eq152628 eq30
    | (have j1 := eq152628 X0
       grind)
    | exact resolve eq30 eq152628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq152628
  have eq155008 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq154958 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154958
    | (have j0 := eq154958 X0
       grind)
    | exact resolve eq154958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154958
  have eq454127 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq122637
       grind)
    | exact superpose eq122637 eq16
    | exact resolve eq16 eq122637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122637
  have eq454398 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq69183 eq454127
    | (have j1 := eq69183 (σ x)
       grind)
    | exact resolve eq454127 eq69183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69183 eq454127
  have eq454399 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq454398
  have eq454425 : x = (k x (τ (σ x))) ∨ x = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq155008 x
       have i₂ := eq454399
       grind)
    | exact superpose eq454399 eq155008
    | (have j0 := eq155008 x
       grind)
    | exact resolve eq155008 eq454399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155008 eq454399
  have eq454800 : x = (k x (τ (σ x))) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq454425
       have r₂ := eq121866
       grind)
    | exact resolve eq454425 eq121866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121866 eq454425
  have eq454843 : x = (k x x) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq454800
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq454800
    | exact resolve eq454800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454800
  have eq454844 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq454843
  have eq455000 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq454844
       grind)
    | exact superpose eq454844 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq454844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454844
  have eq455001 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq455000
  have eq455055 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq455001
       grind)
    | exact superpose eq455001 eq68
    | exact resolve eq68 eq455001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq455001
  have eq455255 : x = (M.op x x) := by grind
  clear eq455055
  have eq455640 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq70 x x X0
       have i₂ := eq455255
       grind)
    | exact superpose eq455255 eq70
    | exact resolve eq70 eq455255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455255
  have eq455906 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq455640 X0
       have i₂ := eq66 x X0
       grind)
    | exact superpose eq66 eq455640
    | exact resolve eq455640 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455640
  have eq458008 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq455906 y
       grind)
    | exact superpose eq455906 eq16
    | exact resolve eq16 eq455906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458015 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq645 x
       have i₂ := eq455906 x
       grind)
    | exact superpose eq455906 eq645
    | exact resolve eq645 eq455906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq455906
  have eq458260 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq458015
  have eq458332 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq458260
  have eq460560 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq70 (σ x) (σ x) X0
       have i₂ := eq458332
       grind)
    | exact superpose eq458332 eq70
    | exact resolve eq70 eq458332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq458332
  have eq460825 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq460560 X0
       have i₂ := eq66 (σ x) X0
       grind)
    | exact superpose eq66 eq460560
    | exact resolve eq460560 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq460560
  have eq460882 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq458008
       have i₂ := eq460825 (σ y)
       grind)
    | exact superpose eq460825 eq458008
    | (have r₁ := eq458008
       have r₂ := eq460825 (σ y)
       grind)
    | exact resolve eq458008 eq460825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458008 eq460825
  have eq461158 : False := by grind
  exact eq461158

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq452 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq452 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq455 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq453 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq453 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq453 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq472 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq455 (σ X0)
       grind)
    | exact superpose eq455 eq15
    | exact resolve eq15 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq472 X0
       have i₂ := eq455 X0
       grind)
    | exact superpose eq455 eq472
    | exact resolve eq472 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq472
  have eq537 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq64
    | exact resolve eq64 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq547 X0 X1
       have j1 := eq548 X0 X1
       grind)
    | (have r₁ := eq547 X0 X1
       have r₂ := eq548 X0 X1
       grind)
    | exact resolve eq547 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq548
  have eq1059 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq549 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq549
    | exact resolve eq549 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1070 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq549 X0 (σ X1)
       grind)
    | exact superpose eq549 eq15
    | (have j1 := eq549 X0 (σ X1)
       grind)
    | exact resolve eq15 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq1089 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1070 X0 X1
       have i₂ := eq491 X1
       grind)
    | exact superpose eq491 eq1070
    | (have j0 := eq1070 X0 X1
       grind)
    | exact resolve eq1070 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq1070
  have eq1107 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq1059 (τ X0) X1
       grind)
    | exact superpose eq1059 eq19
    | (have j1 := eq1059 (τ X0) X1
       grind)
    | exact resolve eq19 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1059
  have eq1614 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1107 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1107
    | exact resolve eq1107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1695 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1614 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1614
    | (have j0 := eq1614 X0 X1
       grind)
    | exact resolve eq1614 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq2829 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1089 x y
       grind)
    | exact superpose eq1089 eq16
    | (have j1 := eq1089 x y
       grind)
    | exact resolve eq16 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq2975 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2829
       have i₂ := eq1695 x y
       grind)
    | exact superpose eq1695 eq2829
    | (have j1 := eq1695 x y
       grind)
    | (have r₁ := eq2829
       have r₂ := eq1695 x y
       grind)
    | exact resolve eq2829 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695 eq2829
  have eq2976 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2975
  have eq2986 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq537 y
       have i₂ := eq2976
       grind)
    | exact superpose eq2976 eq537
    | exact resolve eq537 eq2976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3015 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq64 y y
       have i₂ := eq2976
       grind)
    | exact superpose eq2976 eq64
    | exact resolve eq64 eq2976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq3067 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2986
       grind)
    | exact superpose eq2986 eq16
    | exact resolve eq16 eq2986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq3111 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3067
       have i₂ := eq3015
       grind)
    | exact superpose eq3015 eq3067
    | exact resolve eq3067 eq3015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015 eq3067
  have eq3112 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq3111
  have eq3113 : (σ x) = (σ (M.op y y)) := by grind
  clear eq3112
  have eq3117 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq537 y
       have i₂ := eq3113
       grind)
    | exact superpose eq3113 eq537
    | exact resolve eq537 eq3113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq3130 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3113
       grind)
    | exact superpose eq3113 eq10
    | exact resolve eq10 eq3113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113
  have eq3186 : x = (M.op y y) := by
    first
    | (have i₁ := eq3130
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3130
    | exact resolve eq3130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130
  have eq3222 : y = (M.op x y) := by
    first
    | (have i₁ := eq64 y y
       have i₂ := eq3186
       grind)
    | exact superpose eq3186 eq64
    | exact resolve eq64 eq3186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq3186
  have eq3277 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3117
       grind)
    | exact superpose eq3117 eq16
    | exact resolve eq16 eq3117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3117
  have eq3305 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq3277
       have i₂ := eq3222
       grind)
    | exact superpose eq3222 eq3277
    | exact resolve eq3277 eq3222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3222 eq3277
  have eq3306 : False := by grind
  exact eq3306

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_x_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq37 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq76 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq48 (σ X0)
       grind)
    | exact superpose eq48 eq15
    | (have j1 := eq48 (σ X0)
       grind)
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq237 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq261 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq237 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq262 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq266 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq262
    | (have j0 := eq262 X0 X1
       grind)
    | exact resolve eq262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq267 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq711 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq722 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq711 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq711
    | (have j0 := eq711 (τ X0)
       grind)
    | exact resolve eq711 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq722 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq722
    | (have j0 := eq722 X0
       grind)
    | exact resolve eq722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq726 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq723 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq723
    | (have j0 := eq723 X0
       grind)
    | exact resolve eq723 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq732 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq726 (τ X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq726
    | (have j0 := eq726 (τ X0)
       grind)
    | exact resolve eq726 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq726
  have eq835 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq267 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq267
    | exact resolve eq267 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq267 x y
       grind)
    | exact superpose eq267 eq16
    | (have j1 := eq267 x x
       grind)
    | exact resolve eq16 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq877 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq835 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq835
    | (have j0 := eq835 X0 X1
       grind)
    | exact resolve eq835 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq835
  have eq878 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq877 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq877
    | (have j0 := eq877 X1 X1
       grind)
    | exact resolve eq877 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq938 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq878 (τ X1) X0
       grind)
    | exact superpose eq878 eq17
    | (have j1 := eq878 X0 X0
       grind)
    | exact resolve eq17 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq878
  have eq1244 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq938 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq938
    | (have j0 := eq938 X1 X1
       grind)
    | exact resolve eq938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq1306 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1244 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1244
    | (have j0 := eq1244 X0 X1
       grind)
    | exact resolve eq1244 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1487 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq847
       have i₂ := eq1306 y x
       grind)
    | exact superpose eq1306 eq847
    | (have j1 := eq1306 x (σ x)
       grind)
    | (have r₁ := eq847
       have r₂ := eq1306 y x
       grind)
    | exact resolve eq847 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847 eq1306
  have eq1488 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1487
  have eq1508 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq1488
       grind)
    | exact superpose eq1488 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq1488
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq1488
       grind)
    | exact resolve eq12 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1536 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1508 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508
  have eq1560 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq711 x
       have i₂ := eq1536 x
       grind)
    | exact superpose eq1536 eq711
    | (have j0 := eq711 x
       grind)
    | exact resolve eq711 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq1536
  have eq1578 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1560
  have eq1579 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1578
  have eq1689 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq1579
       grind)
    | exact superpose eq1579 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq1579
       grind)
    | exact resolve eq12 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1696 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 (σ x) (σ x) X0
       have i₂ := eq1579
       grind)
    | exact superpose eq1579 eq37
    | exact resolve eq37 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579
  have eq1719 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq1689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1729 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1696 X0
       have i₂ := eq33 (σ x) X0
       grind)
    | exact superpose eq33 eq1696
    | exact resolve eq1696 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq1752 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq732 (σ x)
       have i₂ := eq1719 (σ x)
       grind)
    | exact superpose eq1719 eq732
    | (have j0 := eq732 (σ x)
       grind)
    | exact resolve eq732 eq1719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq1719
  have eq1776 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by grind
  clear eq1752
  have eq1786 : x = (M.op x x) := by
    first
    | (have i₁ := eq1776
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1776
    | exact resolve eq1776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776
  have eq1866 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 x x X0
       have i₂ := eq1786
       grind)
    | exact superpose eq1786 eq37
    | exact resolve eq37 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1786
  have eq1899 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1866 X0
       have i₂ := eq33 x X0
       grind)
    | exact superpose eq33 eq1866
    | exact resolve eq1866 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1866
  have eq2157 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1729 (σ y)
       grind)
    | exact superpose eq1729 eq16
    | exact resolve eq16 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq2208 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2157
       have i₂ := eq1899 y
       grind)
    | exact superpose eq1899 eq2157
    | exact resolve eq2157 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq2157
  have eq2209 : False := by grind
  exact eq2209

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq167 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq71
    | exact resolve eq71 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1) (σ X0)
       have i₂ := eq71 X1 X0
       grind)
    | exact superpose eq71 eq21
    | (have j1 := eq71 X1 X1
       grind)
    | exact resolve eq21 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq71 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq71 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq71 X0 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq184 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq186 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq184 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq184 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq276 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq186 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq186
    | (have j0 := eq186 (τ X0) X1
       grind)
    | exact resolve eq186 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq278 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq276
    | (have j0 := eq276 X0 X1
       grind)
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq281 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | (have j0 := eq278 X0 X1
       grind)
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq2430 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq176 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2431 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2430 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430
  have eq2474 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) (σ X0) X1
       have i₂ := eq2431 X0
       grind)
    | exact superpose eq2431 eq25
    | (have j1 := eq2431 X0
       grind)
    | exact resolve eq25 eq2431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2431
  have eq2532 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2474 X0 X1
       have i₂ := eq21 (σ X0) X1
       grind)
    | exact superpose eq21 eq2474
    | (have j0 := eq2474 X0 X1
       grind)
    | exact resolve eq2474 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq2770 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2532 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2532
    | (have j0 := eq2532 (k (τ X0) (τ X0)) X0
       grind)
    | exact resolve eq2532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532
  have eq2832 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2770 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2770
    | (have j0 := eq2770 (k (σ (τ X0)) X0) X0
       grind)
    | exact resolve eq2770 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2770
  have eq2837 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2832 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2832
    | (have j0 := eq2832 (k X0 X0) X0
       grind)
    | exact resolve eq2832 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2832
  have eq2929 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (k X0 X0) X0
       have i₂ := eq2837 X0 X1
       grind)
    | exact superpose eq2837 eq21
    | (have j1 := eq2837 X0 (k X0 X0)
       grind)
    | exact resolve eq21 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837
  have eq3051 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2929 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq3052 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3051 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051
  have eq3148 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0 (k X0 X0)
       have i₂ := eq3052 X0
       grind)
    | exact superpose eq3052 eq21
    | exact resolve eq21 eq3052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3052
  have eq3547 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (k X0 (τ X1))
       have i₂ := eq167 X0 X1 (τ X2)
       grind)
    | exact superpose eq167 eq17
    | (have j1 := eq167 X0 X1 (τ X2)
       grind)
    | exact resolve eq17 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq167
  have eq3579 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3547 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq3547
    | (have j0 := eq3547 X0 X1 X2
       grind)
    | exact resolve eq3547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq3594 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3579 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq3579
    | (have j0 := eq3579 X0 X1 X2
       grind)
    | exact resolve eq3579 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3579
  have eq3602 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3594 X0 X1 X2
       have j1 := eq12 X2 (k (σ X0) X1)
       grind)
    | (have r₁ := eq3594 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X0) X1)
       grind)
    | exact resolve eq3594 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594
  have eq3610 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3602 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq3602
    | (have j0 := eq3602 X0 X1 X2
       grind)
    | exact resolve eq3602 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3602
  have eq17941 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op (k X0 X2) X1) ∨ (k X1 (k X0 X2)) = (M.op (k X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3610 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3610
    | exact resolve eq3610 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3610
  have eq40860 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17941 X0 X0 X0
       have i₂ := eq3148 X0
       grind)
    | exact superpose eq3148 eq17941
    | exact resolve eq17941 eq3148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3148
  have eq40909 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X2 (k X0 X1)) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (k X0 X2) X1
       have i₂ := eq17941 X0 X1 X2
       grind)
    | exact superpose eq17941 eq23
    | (have j1 := eq17941 X0 (k X0 X1) X1
       grind)
    | exact resolve eq23 eq17941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17941
  have eq41138 : ∀ X0 X1 X2 : G, (k X2 (k X0 X1)) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40909 X0 X1 X2
       have j1 := eq12 X2 (k X0 X1)
       grind)
    | (have r₁ := eq40909 X0 X1 X2
       have r₂ := eq12 X0 (k X0 X1)
       grind)
    | exact resolve eq40909 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40909
  have eq41799 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41138 X0 (k X0 X0) x
       have i₂ := eq40860 X0
       grind)
    | exact superpose eq40860 eq41138
    | (have j1 := eq40860 X0
       grind)
    | exact resolve eq41138 eq40860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40860 eq41138
  have eq41901 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41799 X0 X1
       have j1 := eq281 X0 X1
       grind)
    | (have r₁ := eq41799 X0 X1
       have r₂ := eq281 X0 X1
       grind)
    | exact resolve eq41799 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq41799
  have eq42359 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq41901 (σ X0) (σ X1)
       grind)
    | exact superpose eq41901 eq15
    | exact resolve eq15 eq41901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42486 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42359 X0 X1
       have i₂ := eq41901 X0 X1
       grind)
    | exact superpose eq41901 eq42359
    | exact resolve eq42359 eq41901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41901 eq42359
  have eq47466 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42486 x y
       grind)
    | exact superpose eq42486 eq16
    | (have r₁ := eq16
       have r₂ := eq42486 x y
       grind)
    | exact resolve eq16 eq42486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42486
  have eq47631 : False := by grind
  exact eq47631

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq162 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq68
    | exact resolve eq68 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1) (σ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq21
    | (have j1 := eq68 X1 X1
       grind)
    | exact resolve eq21 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq68 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq179 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq175 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq181 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq179 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq179 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq179 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq271 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq181 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq181
    | (have j0 := eq181 (τ X0) X1
       grind)
    | exact resolve eq181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq273 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq271 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq271
    | (have j0 := eq271 X0 X1
       grind)
    | exact resolve eq271 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq276 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq273 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq273
    | (have j0 := eq273 X0 X1
       grind)
    | exact resolve eq273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq2313 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq171 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq2314 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2313 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2313
  have eq2356 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) (σ X0) X1
       have i₂ := eq2314 X0
       grind)
    | exact superpose eq2314 eq25
    | (have j1 := eq2314 X0
       grind)
    | exact resolve eq25 eq2314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2314
  have eq2414 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2356 X0 X1
       have i₂ := eq21 (σ X0) X1
       grind)
    | exact superpose eq21 eq2356
    | (have j0 := eq2356 X0 X1
       grind)
    | exact resolve eq2356 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356
  have eq2650 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2414 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2414
    | (have j0 := eq2414 (k (τ X0) (τ X0)) X0
       grind)
    | exact resolve eq2414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414
  have eq2711 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2650 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2650
    | (have j0 := eq2650 (k (σ (τ X0)) X0) X0
       grind)
    | exact resolve eq2650 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650
  have eq2715 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2711 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2711
    | (have j0 := eq2711 (k X0 X0) X0
       grind)
    | exact resolve eq2711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2790 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (k X0 X0) X0
       have i₂ := eq2715 X0 X1
       grind)
    | exact superpose eq2715 eq21
    | (have j1 := eq2715 X0 (k X0 X0)
       grind)
    | exact resolve eq21 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2715
  have eq2912 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2790 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790
  have eq2913 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2912 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2912
  have eq3008 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0 (k X0 X0)
       have i₂ := eq2913 X0
       grind)
    | exact superpose eq2913 eq21
    | exact resolve eq21 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2913
  have eq3398 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (k X0 (τ X1))
       have i₂ := eq162 X0 X1 (τ X2)
       grind)
    | exact superpose eq162 eq17
    | (have j1 := eq162 X0 X1 (τ X2)
       grind)
    | exact resolve eq17 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq162
  have eq3428 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3398 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq3398
    | (have j0 := eq3398 X0 X1 X2
       grind)
    | exact resolve eq3398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398
  have eq3440 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3428 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq3428
    | (have j0 := eq3428 X0 X1 X2
       grind)
    | exact resolve eq3428 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3428
  have eq3446 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3440 X0 X1 X2
       have j1 := eq12 X2 (k (σ X0) X1)
       grind)
    | (have r₁ := eq3440 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X0) X1)
       grind)
    | exact resolve eq3440 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3440
  have eq3452 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3446 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq3446
    | (have j0 := eq3446 X0 X1 X2
       grind)
    | exact resolve eq3446 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq17453 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op (k X0 X2) X1) ∨ (k X1 (k X0 X2)) = (M.op (k X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3452 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3452
    | exact resolve eq3452 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3452
  have eq40647 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17453 X0 X0 X0
       have i₂ := eq3008 X0
       grind)
    | exact superpose eq3008 eq17453
    | exact resolve eq17453 eq3008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008
  have eq40696 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X2 (k X0 X1)) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (k X0 X2) X1
       have i₂ := eq17453 X0 X1 X2
       grind)
    | exact superpose eq17453 eq23
    | (have j1 := eq17453 X0 (k X0 X1) X1
       grind)
    | exact resolve eq23 eq17453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17453
  have eq40925 : ∀ X0 X1 X2 : G, (k X2 (k X0 X1)) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40696 X0 X1 X2
       have j1 := eq12 X2 (k X0 X1)
       grind)
    | (have r₁ := eq40696 X0 X1 X2
       have r₂ := eq12 X0 (k X0 X1)
       grind)
    | exact resolve eq40696 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40696
  have eq41638 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40925 X0 (k X0 X0) x
       have i₂ := eq40647 X0
       grind)
    | exact superpose eq40647 eq40925
    | (have j1 := eq40647 X0
       grind)
    | exact resolve eq40925 eq40647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40647 eq40925
  have eq41740 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41638 X0 X1
       have j1 := eq276 X0 X1
       grind)
    | (have r₁ := eq41638 X0 X1
       have r₂ := eq276 X0 X1
       grind)
    | exact resolve eq41638 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq41638
  have eq42193 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq41740 (σ X0) (σ X1)
       grind)
    | exact superpose eq41740 eq15
    | exact resolve eq15 eq41740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42321 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42193 X0 X1
       have i₂ := eq41740 X0 X1
       grind)
    | exact superpose eq41740 eq42193
    | exact resolve eq42193 eq41740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41740 eq42193
  have eq49042 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42321 x y
       grind)
    | exact superpose eq42321 eq16
    | (have r₁ := eq16
       have r₂ := eq42321 x y
       grind)
    | exact resolve eq16 eq42321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42321
  have eq49207 : False := by grind
  exact eq49207
