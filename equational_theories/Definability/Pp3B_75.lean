import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_y_pyx_pxx_pyx_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq29 (σ X0)
       grind)
    | exact superpose eq29 eq15
    | exact resolve eq15 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq29 (τ X0)
       grind)
    | exact superpose eq29 eq18
    | exact resolve eq18 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq31
    | exact resolve eq31 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq33
    | exact resolve eq33 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq33
  have eq49 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq73 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq21
    | exact resolve eq21 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq138 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq390 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | (have j0 := eq54 X1 (τ X0)
       grind)
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq417 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq390 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq390
    | (have j0 := eq390 X0 X1
       grind)
    | exact resolve eq390 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq390
  have eq423 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq417 X0 X1
       have j1 := eq73 X1 X0
       grind)
    | (have r₁ := eq417 X1 X0
       have r₂ := eq73 X0 X1
       grind)
    | exact resolve eq417 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq417
  have eq427 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq423
    | (have j0 := eq423 X0 X1
       grind)
    | exact resolve eq423 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq423
  have eq595 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq427
    | exact resolve eq427 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq427 (σ X1) X0
       grind)
    | exact superpose eq427 eq15
    | (have j1 := eq427 (σ X1) X0
       grind)
    | exact resolve eq15 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq616 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq605
    | (have j0 := eq605 X0 X1
       grind)
    | exact resolve eq605 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq605
  have eq630 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq595 (τ X0) X1
       grind)
    | exact superpose eq595 eq19
    | (have j1 := eq595 (τ X0) X1
       grind)
    | exact resolve eq19 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq595
  have eq1372 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq630 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq630
    | exact resolve eq630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq1435 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1372 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1372
    | (have j0 := eq1372 X0 X1
       grind)
    | exact resolve eq1372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq1842 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq138 x X2 X0 X1
       grind)
    | exact superpose eq138 eq9
    | exact resolve eq9 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq1901 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1842 x X1 X0
       grind)
    | exact superpose eq1842 eq9
    | exact resolve eq9 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq2113 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq616 x y
       grind)
    | exact superpose eq616 eq16
    | (have j1 := eq616 x y
       grind)
    | exact resolve eq16 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq2278 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2113
       have i₂ := eq1435 x y
       grind)
    | exact superpose eq1435 eq2113
    | (have j1 := eq1435 x y
       grind)
    | (have r₁ := eq2113
       have r₂ := eq1435 x y
       grind)
    | exact resolve eq2113 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq2113
  have eq2279 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2278
  have eq2285 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2279
       grind)
    | exact superpose eq2279 eq10
    | exact resolve eq10 eq2279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2279
  have eq2332 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2285
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2285
    | exact resolve eq2285 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285
  have eq2333 : x = (M.op y y) := by grind
  clear eq2332
  have eq2346 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74 y
       have i₂ := eq2333
       grind)
    | exact superpose eq2333 eq74
    | exact resolve eq74 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq2370 : x = (M.op x y) := by
    first
    | (have i₁ := eq1901 y y
       have i₂ := eq2333
       grind)
    | exact superpose eq2333 eq1901
    | exact resolve eq1901 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901 eq2333
  have eq2474 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2346
       grind)
    | exact superpose eq2346 eq16
    | exact resolve eq16 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346
  have eq2490 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2474
       have i₂ := eq2370
       grind)
    | exact superpose eq2370 eq2474
    | exact resolve eq2474 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370 eq2474
  have eq2491 : False := by grind
  exact eq2491

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq30
    | exact resolve eq30 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq30
  have eq65 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq33 X1
       grind)
    | exact superpose eq33 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq216 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq13
    | (have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq220 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq226 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq217 X0 X1
       have j1 := eq65 X1 (σ X0)
       grind)
    | (have r₁ := eq217 X0 X0
       have r₂ := eq65 X0 (σ X0)
       grind)
    | exact resolve eq217 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq227 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq220 X0 X1
       have j1 := eq65 X1 (σ X0)
       grind)
    | (have r₁ := eq220 X0 X0
       have r₂ := eq65 X0 (σ X0)
       grind)
    | exact resolve eq220 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq220
  have eq242 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq33 X1
       grind)
    | exact superpose eq33 eq226
    | (have j0 := eq226 X0 X1
       grind)
    | exact resolve eq226 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq243 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq227 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq227
    | (have j0 := eq227 X0 X1
       grind)
    | exact resolve eq227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq244 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq243 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq253 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq242
    | (have j0 := eq242 X0 X1
       grind)
    | exact resolve eq242 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq254 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq253 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq33 X1
       grind)
    | exact superpose eq33 eq244
    | (have j0 := eq244 X0 X1
       grind)
    | exact resolve eq244 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq244
  have eq261 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       have j1 := eq254 X0 X1
       grind)
    | (have r₁ := eq255 X0 X1
       have r₂ := eq254 X0 X1
       grind)
    | exact resolve eq255 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq255
  have eq263 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq261
    | exact resolve eq261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq261 x y
       grind)
    | exact superpose eq261 eq16
    | exact resolve eq16 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq365 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq263 X0 (τ X1)
       grind)
    | exact superpose eq263 eq18
    | exact resolve eq18 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq263
  have eq384 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq365
    | exact resolve eq365 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq393 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq384
    | exact resolve eq384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq414 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq275
       have i₂ := eq393 x y
       grind)
    | exact superpose eq393 eq275
    | exact resolve eq275 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq393
  have eq415 : False := by grind
  exact eq415

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq296 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq296 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq302 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq301 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq428 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq302 X0 X1
       grind)
    | exact superpose eq302 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq302 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq302 X0 X1
       grind)
    | exact resolve eq13 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq302 (σ x) (σ y)
       grind)
    | exact superpose eq302 eq16
    | (have j1 := eq302 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq436 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq430
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq430
    | exact resolve eq430 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq437 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq433 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq433 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq451 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq437 X0 (τ X1)
       grind)
    | exact superpose eq437 eq18
    | (have j1 := eq437 X0 (τ X1)
       grind)
    | exact resolve eq18 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq468 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq437 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq451 (τ X0) X1
       grind)
    | exact superpose eq451 eq17
    | (have j1 := eq451 (τ X0) X1
       grind)
    | exact resolve eq17 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq451
  have eq1404 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1399 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1399
    | (have j0 := eq1399 X0 X1
       grind)
    | exact resolve eq1399 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1418 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1404 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1404
    | (have j0 := eq1404 X0 X1
       grind)
    | exact resolve eq1404 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1421 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1418 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1418
    | (have j0 := eq1418 X0 X1
       grind)
    | exact resolve eq1418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1487 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1421 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1421
    | (have j0 := eq1421 X1 (σ X0)
       grind)
    | exact resolve eq1421 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq1915 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1487 X0 X0
       have i₂ := eq437 X0 (σ X0)
       grind)
    | exact superpose eq437 eq1487
    | (have j0 := eq1487 X1 X0
       have j1 := eq437 X0 (σ X1)
       grind)
    | exact resolve eq1487 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq1487
  have eq1951 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1915 X0 X1
       have j1 := eq468 X0 (σ X1)
       grind)
    | (have r₁ := eq1915 X0 X1
       have r₂ := eq468 X0 (σ X1)
       grind)
    | exact resolve eq1915 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq1915
  have eq2341 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1951 (σ X0) X1
       grind)
    | exact superpose eq1951 eq28
    | (have j1 := eq1951 (σ X0) X1
       grind)
    | exact resolve eq28 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1951
  have eq2352 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2341 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2341
    | (have j0 := eq2341 X0 X1
       grind)
    | exact resolve eq2341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341
  have eq2366 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2352 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2352
    | (have j0 := eq2352 X0 X1
       grind)
    | exact resolve eq2352 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352
  have eq2375 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2366 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2366
    | (have j0 := eq2366 X0 X1
       grind)
    | exact resolve eq2366 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2504 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2375 x y
       grind)
    | exact superpose eq2375 eq16
    | (have j1 := eq2375 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2375 x y
       grind)
    | exact resolve eq16 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2551 : x = (k x y) := by grind
  clear eq2504
  have eq2742 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq436
       have i₂ := eq302 x y
       grind)
    | exact superpose eq302 eq436
    | (have j1 := eq302 x y
       grind)
    | exact resolve eq436 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2744 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq2742
  have eq2745 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2744
       have i₂ := eq2551
       grind)
    | exact superpose eq2551 eq2744
    | exact resolve eq2744 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744
  have eq2746 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2745
       have i₂ := eq2551
       grind)
    | exact superpose eq2551 eq2745
    | exact resolve eq2745 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2745
  have eq2748 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq436
       have i₂ := eq2746
       grind)
    | exact superpose eq2746 eq436
    | exact resolve eq436 eq2746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq2746
  have eq2759 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2748
  have eq2760 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2759
       have i₂ := eq2551
       grind)
    | exact superpose eq2551 eq2759
    | exact resolve eq2759 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq2761 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2760
  have eq2765 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2761
       grind)
    | exact superpose eq2761 eq16
    | exact resolve eq16 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761
  have eq2789 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2765
       have i₂ := eq302 x y
       grind)
    | exact superpose eq302 eq2765
    | (have j1 := eq302 x y
       grind)
    | exact resolve eq2765 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq2791 : (M.op x y) = (k x y) := by grind
  clear eq2789
  have eq2793 : x = (M.op x y) := by
    first
    | (have i₁ := eq2791
       have i₂ := eq2551
       grind)
    | exact superpose eq2551 eq2791
    | exact resolve eq2791 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551 eq2791
  have eq2795 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2765
       have i₂ := eq2793
       grind)
    | exact superpose eq2793 eq2765
    | exact resolve eq2765 eq2793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765 eq2793
  have eq2808 : False := by grind
  exact eq2808

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq421 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq421 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq428 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq427 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq575 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq428 X1 X0
       grind)
    | exact superpose eq428 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq428 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq428 X0 X1
       grind)
    | exact resolve eq13 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq428 (σ y) (σ x)
       grind)
    | exact superpose eq428 eq16
    | (have j1 := eq428 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq575 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq585 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq577
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq577
    | exact resolve eq577 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq586 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq583 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq583 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq583 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq600 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq586 X0 (τ X1)
       grind)
    | exact superpose eq586 eq18
    | (have j1 := eq586 X0 (τ X1)
       grind)
    | exact resolve eq18 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq621 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq586 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2263 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq600 (τ X0) X1
       grind)
    | exact superpose eq600 eq17
    | (have j1 := eq600 (τ X0) X1
       grind)
    | exact resolve eq17 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq600
  have eq2268 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2263 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2263
    | (have j0 := eq2263 X0 X1
       grind)
    | exact resolve eq2263 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq2286 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2268 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2268
    | (have j0 := eq2268 X0 X1
       grind)
    | exact resolve eq2268 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268
  have eq2291 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2286 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2286
    | (have j0 := eq2286 X0 X1
       grind)
    | exact resolve eq2286 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq2367 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2291 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2291
    | (have j0 := eq2291 X1 (σ X0)
       grind)
    | exact resolve eq2291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291
  have eq2816 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2367 X0 X0
       have i₂ := eq586 X0 (σ X0)
       grind)
    | exact superpose eq586 eq2367
    | (have j0 := eq2367 X1 X0
       have j1 := eq586 X0 (σ X1)
       grind)
    | exact resolve eq2367 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq2367
  have eq2858 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2816 X0 X1
       have j1 := eq621 X0 (σ X1)
       grind)
    | (have r₁ := eq2816 X0 X1
       have r₂ := eq621 X0 (σ X1)
       grind)
    | exact resolve eq2816 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq2816
  have eq3352 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq2858 (σ X0) X1
       grind)
    | exact superpose eq2858 eq28
    | (have j1 := eq2858 (σ X0) X1
       grind)
    | exact resolve eq28 eq2858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2858
  have eq3363 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3352 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3352
    | (have j0 := eq3352 X0 X1
       grind)
    | exact resolve eq3352 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq3381 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3363 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3363
    | (have j0 := eq3363 X0 X1
       grind)
    | exact resolve eq3363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363
  have eq3392 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3381 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3381
    | (have j0 := eq3381 X0 X1
       grind)
    | exact resolve eq3381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381
  have eq3513 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3392 x y
       grind)
    | exact superpose eq3392 eq16
    | (have j1 := eq3392 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3392 x y
       grind)
    | exact resolve eq16 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392
  have eq3575 : x = (k x y) := by grind
  clear eq3513
  have eq4088 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq585
       have i₂ := eq428 y x
       grind)
    | exact superpose eq428 eq585
    | (have j1 := eq428 y x
       grind)
    | exact resolve eq585 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4091 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq4088
  have eq4092 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4091
       have i₂ := eq3575
       grind)
    | exact superpose eq3575 eq4091
    | exact resolve eq4091 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4091
  have eq4093 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4092
       have i₂ := eq3575
       grind)
    | exact superpose eq3575 eq4092
    | exact resolve eq4092 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4092
  have eq4094 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq585
       have i₂ := eq4093
       grind)
    | exact superpose eq4093 eq585
    | exact resolve eq585 eq4093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq4093
  have eq4107 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4094
  have eq4109 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4107
       have i₂ := eq3575
       grind)
    | exact superpose eq3575 eq4107
    | exact resolve eq4107 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4107
  have eq4110 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4109
  have eq4112 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4110
       grind)
    | exact superpose eq4110 eq16
    | exact resolve eq16 eq4110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4110
  have eq4137 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4112
       have i₂ := eq428 y x
       grind)
    | exact superpose eq428 eq4112
    | (have j1 := eq428 y x
       grind)
    | exact resolve eq4112 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq4140 : (M.op x y) = (k x y) := by grind
  clear eq4137
  have eq4142 : x = (M.op x y) := by
    first
    | (have i₁ := eq4140
       have i₂ := eq3575
       grind)
    | exact superpose eq3575 eq4140
    | exact resolve eq4140 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3575 eq4140
  have eq4143 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4112
       have i₂ := eq4142
       grind)
    | exact superpose eq4142 eq4112
    | exact resolve eq4112 eq4142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4112 eq4142
  have eq4158 : False := by grind
  exact eq4158

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op X1 (M.op X2 (M.op X0 X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 (M.op X0 X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
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
  have eq73 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq169 : ∀ X0 X1 X2 : G, (σ X0) = (k (M.op X1 (M.op X2 (σ (k X0 X0)))) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (σ X1) X1 X2
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq46
    | (have j0 := eq46 (σ X0) X1 X2
       have j1 := eq71 X0 X0
       grind)
    | exact resolve eq46 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq177 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq178 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq184 : ∀ X0 X1 X2 : G, (σ X0) = (k (M.op X1 (M.op X2 (σ (k X0 X0)))) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq169 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq187 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (M.op X1 (M.op X2 (σ (k X0 X0)))) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq184 X0 X1 X2
       have j1 := eq178 X0
       grind)
    | (have r₁ := eq184 X0 X1 X2
       have r₂ := eq178 X0
       grind)
    | exact resolve eq184 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq184
  have eq408 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | (have j0 := eq73 X1 X1
       grind)
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq440 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq408
    | (have j0 := eq408 X0 X1
       grind)
    | exact resolve eq408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq718 : ∀ X0 X1 X2 X3 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (k (M.op X2 (M.op X3 (σ (k X0 X0)))) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq187 X0 X2 X3
       grind)
    | exact superpose eq187 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq187 X0 X2 X3
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq187 X0 X1 X2
       grind)
    | exact resolve eq12 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq724 : ∀ X0 X1 X2 X3 : G, (σ X0) = (k (M.op X2 (M.op X3 (σ (k X0 X0)))) (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq718 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq855 : ∀ X0 X1 X2 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) X2) ∨ (k (σ X2) X0) = (σ (M.op (τ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq75 X0 X2
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq75 X0 X2
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq75 X0 (τ X0)
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq75 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq863 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq864 : ∀ X0 X1 X2 : G, (k (σ X2) X0) = (σ (M.op (τ X0) X2)) ∨ (τ X0) = (M.op (τ X0) X2) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq855 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq865 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq863 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq863
    | (have j0 := eq863 X0
       grind)
    | exact resolve eq863 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq898 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq865 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq865
    | exact resolve eq865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq915 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq898 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq898
    | (have j0 := eq898 X0
       grind)
    | exact resolve eq898 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq960 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq82 x X2 X0 X1
       grind)
    | exact superpose eq82 eq9
    | exact resolve eq9 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1005 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq960 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq960 eq9
    | exact resolve eq9 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1063 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq915 X0
       grind)
    | exact superpose eq915 eq10
    | (have j1 := eq915 X0
       grind)
    | exact resolve eq10 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq1103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1063 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1063
    | (have j0 := eq1063 X0
       grind)
    | exact resolve eq1063 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1103 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1103 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1103 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1133 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1109 (σ X0)
       grind)
    | exact superpose eq1109 eq15
    | exact resolve eq15 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq1109 (τ X0)
       grind)
    | exact superpose eq1109 eq35
    | exact resolve eq35 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1150 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1140 X0
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq1140
    | exact resolve eq1140 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1156 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1133 X0
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq1133
    | exact resolve eq1133 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1298 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq1156 X0
       grind)
    | exact superpose eq1156 eq9
    | exact resolve eq9 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq2402 : ∀ X0 X1 X2 : G, (k (τ X2) (k X1 X0)) = (τ (k X2 (σ (M.op X0 X1)))) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 (k X1 X0)
       have i₂ := eq440 X1 X0
       grind)
    | exact superpose eq440 eq26
    | (have j1 := eq440 X1 X0
       grind)
    | exact resolve eq26 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq2454 : ∀ X0 X1 X2 : G, (k (τ X2) (k X1 X0)) = (k (τ X2) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2402 X0 X1 X2
       have i₂ := eq26 X2 (M.op X0 X1)
       grind)
    | exact superpose eq26 eq2402
    | (have j0 := eq2402 X0 X1 X2
       grind)
    | exact resolve eq2402 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2402
  have eq7782 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq960 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1005 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1005 eq960
    | exact resolve eq960 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq1005
  have eq14276 : ∀ X0 X1 X2 : G, (σ X2) ≠ (M.op (σ X2) (M.op X0 (M.op X1 (σ (k X2 X2))))) ∨ (M.op (σ X2) (M.op X0 (M.op X1 (σ (k X2 X2))))) = (k (M.op X0 (M.op X1 (σ (k X2 X2)))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq724 X2 (M.op X0 (M.op X1 (σ (k X2 X2)))) X2 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq14284 : ∀ X0 X1 X2 : G, (σ X2) ≠ (M.op (σ X2) (M.op X0 (M.op X1 (σ (M.op X2 X2))))) ∨ (M.op (σ X2) (M.op X0 (M.op X1 (σ (k X2 X2))))) = (k (M.op X0 (M.op X1 (σ (k X2 X2)))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14276 X0 X1 X2
       have i₂ := eq1109 X2
       grind)
    | exact superpose eq1109 eq14276
    | (have j0 := eq14276 X0 X1 X2
       grind)
    | exact resolve eq14276 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14276
  have eq14350 : ∀ X0 X1 X2 : G, (M.op (σ X2) (M.op X0 (M.op X1 (σ (k X2 X2))))) = (k (M.op X0 (M.op X1 (σ (k X2 X2)))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq14284 X0 X1 X2
       grind)
    | (have r₁ := eq14284 X1 X2 X0
       have r₂ := eq1298 X0 X1 X2
       grind)
    | exact resolve eq14284 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14284
  have eq14406 : ∀ X0 X1 X2 : G, (M.op (σ X2) (M.op X0 (M.op X1 (σ (M.op X2 X2))))) = (k (M.op X0 (M.op X1 (σ (M.op X2 X2)))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14350 X0 X1 X0
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq14350
    | exact resolve eq14350 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq14350
  have eq14435 : ∀ X0 X1 X2 : G, (σ X2) = (k (M.op X0 (M.op X1 (σ (M.op X2 X2)))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14406 X0 X1 X2
       have i₂ := eq1298 X2 X0 X1
       grind)
    | exact superpose eq1298 eq14406
    | exact resolve eq14406 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298 eq14406
  have eq14507 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ X0))))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14435 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14435
    | exact resolve eq14435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14435
  have eq14574 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 (σ (τ (M.op X0 X0))))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14507 X0 X1 X2
       have i₂ := eq1150 X0
       grind)
    | exact superpose eq1150 eq14507
    | exact resolve eq14507 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq14507
  have eq14597 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 (M.op X0 X0))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14574 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq14574
    | exact resolve eq14574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14574
  have eq14656 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14597 (M.op X1 X0) X0 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq7782 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq7782 eq14597
    | exact resolve eq14597 eq7782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7782 eq14597
  have eq14961 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (M.op X0 (σ X1))
       have i₂ := eq14656 (σ X1) X0
       grind)
    | exact superpose eq14656 eq32
    | exact resolve eq32 eq14656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14966 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (M.op X0 (τ X1))
       have i₂ := eq14656 (τ X1) X0
       grind)
    | exact superpose eq14656 eq17
    | exact resolve eq17 eq14656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22927 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq864 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq864
    | exact resolve eq864 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq23106 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22927 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq22927
    | (have j0 := eq22927 X0 X1 X2
       grind)
    | exact resolve eq22927 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22927
  have eq189035 : ∀ X0 X1 X2 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq23106 X0 X1 X2
       grind)
    | exact superpose eq23106 eq10
    | (have j1 := eq23106 X0 X1 X2
       grind)
    | exact resolve eq10 eq23106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23106
  have eq189269 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189035 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq189035
    | (have j0 := eq189035 X0 X1 X1
       grind)
    | exact resolve eq189035 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189035
  have eq190501 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq189269 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189269
  have eq190502 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq190501 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190501
  have eq191360 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 X0
       have i₂ := eq190502 X1 (σ X0)
       grind)
    | exact superpose eq190502 eq26
    | (have j1 := eq190502 X1 (σ X0)
       grind)
    | exact resolve eq26 eq190502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq191375 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) ∨ (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14966 X0 X1
       have i₂ := eq190502 X1 (σ (M.op X0 (τ X1)))
       grind)
    | exact superpose eq190502 eq14966
    | (have j1 := eq190502 X1 (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq14966 eq190502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191401 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (M.op (τ (M.op X0 (σ X1))) X1) ∨ (τ (M.op X0 (σ X1))) = (M.op (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14961 X0 X1
       have i₂ := eq190502 X1 (τ (M.op X0 (σ X1)))
       grind)
    | exact superpose eq190502 eq14961
    | (have j1 := eq190502 X1 (τ (M.op X0 (σ X1)))
       grind)
    | exact resolve eq14961 eq190502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191539 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq190502 (σ X1) X0
       grind)
    | exact superpose eq190502 eq32
    | (have j1 := eq190502 (σ X1) X0
       grind)
    | exact resolve eq32 eq190502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191899 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (M.op (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq191401 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191401
  have eq191901 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq191375 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191375
  have eq195848 : ∀ X0 X1 : G, (τ (M.op X1 X0)) = (M.op (τ (M.op X1 X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq191899 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191899
    | exact resolve eq191899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197466 : ∀ X0 X1 : G, (τ (τ (M.op X0 (σ X1)))) = (M.op (τ (τ (M.op X0 (σ X1)))) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq195848 X1 (τ (M.op X0 (σ X1)))
       have i₂ := eq191899 X0 X1
       grind)
    | exact superpose eq191899 eq195848
    | exact resolve eq195848 eq191899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195848
  have eq199800 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq191901 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq191901
    | exact resolve eq191901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191901
  have eq398290 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k X0 (k X0 (τ X1))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14961 X0 X1
       have i₂ := eq191539 X0 X1
       grind)
    | exact superpose eq191539 eq14961
    | (have j1 := eq191539 X1 X0
       grind)
    | exact resolve eq14961 eq191539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14961 eq191539
  have eq535456 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (M.op (k (τ (σ X0)) X1) X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq191899 (σ X0) X1
       have i₂ := eq191360 X0 (σ X1)
       grind)
    | exact superpose eq191360 eq191899
    | (have j1 := eq191360 X1 (σ X0)
       grind)
    | exact resolve eq191899 eq191360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191360 eq191899
  have eq536118 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq535456 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq535456
    | (have j0 := eq535456 X0 X1
       grind)
    | exact resolve eq535456 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535456
  have eq541849 : ∀ X0 X1 : G, (σ (k (τ X0) (τ X1))) = (k X0 (σ (k (τ X0) (τ X1)))) ∨ (M.op X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (k (τ X0) (τ X1))
       have i₂ := eq398290 (τ X0) X1
       grind)
    | exact superpose eq398290 eq17
    | (have j1 := eq398290 (τ X0) X1
       grind)
    | exact resolve eq17 eq398290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398290
  have eq542007 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (k X0 (k (σ (τ X0)) X1)) ∨ (M.op X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq541849 X0 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq541849
    | (have j0 := eq541849 X0 X1
       grind)
    | exact resolve eq541849 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541849
  have eq542177 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (M.op X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq542007 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq542007
    | (have j0 := eq542007 X0 X1
       grind)
    | exact resolve eq542007 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542007
  have eq542291 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq542177 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq542177
    | (have j0 := eq542177 X0 X1
       grind)
    | exact resolve eq542177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542177
  have eq542923 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190502 X0 (k X0 X1)
       have i₂ := eq542291 X0 X1
       grind)
    | exact superpose eq542291 eq190502
    | (have j0 := eq190502 X0 (k X0 X1)
       have j1 := eq542291 X0 (k X0 X1)
       grind)
    | exact resolve eq190502 eq542291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190502 eq542291
  have eq543087 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq542923 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542923
  have eq600300 : ∀ X0 X1 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (k X1 X0) = (M.op (k X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14656 (σ X0) (σ X1)
       have i₂ := eq536118 X0 X1
       grind)
    | exact superpose eq536118 eq14656
    | (have j1 := eq536118 X1 X0
       grind)
    | exact resolve eq14656 eq536118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536118
  have eq600524 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (M.op (k X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq600300 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq600300
    | (have j0 := eq600300 X0 X1
       grind)
    | exact resolve eq600300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600300
  have eq603550 : ∀ X0 X1 : G, (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (τ (k X0 X1)) = (M.op (τ (k X0 X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq600524 (τ X0) (τ X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq600524
    | exact resolve eq600524 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600524
  have eq604360 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (τ (k X0 X1)) = (M.op (τ (k X0 X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq603550 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq603550
    | (have j0 := eq603550 X0 X1
       grind)
    | exact resolve eq603550 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603550
  have eq604444 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ (k X0 X1)) (τ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq604360 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq604360
    | (have j0 := eq604360 X0 X1
       grind)
    | exact resolve eq604360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604360
  have eq1142554 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k X0 (σ (τ (k X0 X1)))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14966 (τ (k X0 X1)) X0
       have i₂ := eq604444 X0 X1
       grind)
    | exact superpose eq604444 eq14966
    | (have j1 := eq604444 X0 (σ (τ (k X0 X1)))
       grind)
    | exact resolve eq14966 eq604444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14966 eq604444
  have eq1143731 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1142554 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1142554
    | (have j0 := eq1142554 X0 (k X0 X1)
       grind)
    | exact resolve eq1142554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142554
  have eq1146927 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ X0) (M.op X1 (τ X0))) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1143731 (τ X0) X1
       have i₂ := eq2454 X1 (τ X0) X0
       grind)
    | exact superpose eq2454 eq1143731
    | (have j0 := eq1143731 (τ X0) X1
       have j1 := eq2454 X1 (τ X0) x
       grind)
    | exact resolve eq1143731 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454 eq1143731
  have eq1147836 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ X0) (M.op X1 (τ X0))) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1146927 X0 X1
       have j1 := eq13 (τ X0) X1
       grind)
    | (have r₁ := eq1146927 X0 X1
       have r₂ := eq13 (τ X0) X1
       grind)
    | (have r₁ := eq1146927 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq1146927 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146927
  have eq1148259 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1147836 X0 X1
       have i₂ := eq14656 (τ X0) X1
       grind)
    | exact superpose eq14656 eq1147836
    | (have j0 := eq1147836 X0 X1
       grind)
    | exact resolve eq1147836 eq14656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14656 eq1147836
  have eq1148408 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1148259 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq1148259 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1148259 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148259
  have eq1148520 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1148408 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1148408
    | exact resolve eq1148408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148600 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1148408 X1 X0
       grind)
    | exact superpose eq1148408 eq17
    | (have j1 := eq1148408 X1 X0
       grind)
    | exact resolve eq17 eq1148408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1148408
  have eq1154738 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1148520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148520
  have eq1174465 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1148600 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1148600
    | exact resolve eq1148600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174953 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq1148600 (τ X0) X1
       grind)
    | exact superpose eq1148600 eq18
    | (have j1 := eq1148600 (τ X0) X1
       grind)
    | exact resolve eq18 eq1148600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1148600
  have eq1175333 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1174953 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1174953
    | (have j0 := eq1174953 X0 X1
       grind)
    | exact resolve eq1174953 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174953
  have eq1175573 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1174465 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1174465
    | (have j0 := eq1174465 X0 X1
       grind)
    | exact resolve eq1174465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174465
  have eq1175738 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1175333 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1175333
    | (have j0 := eq1175333 X0 X1
       grind)
    | exact resolve eq1175333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175333
  have eq1175999 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1175738 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1175738
    | (have j0 := eq1175738 X0 X1
       grind)
    | exact resolve eq1175738 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175738
  have eq1182525 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) (τ X0))
       have i₂ := eq1175999 X1 X0
       grind)
    | exact superpose eq1175999 eq10
    | (have j1 := eq1175999 X1 X0
       grind)
    | exact resolve eq10 eq1175999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175999
  have eq1183611 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1182525 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1182525
    | (have j0 := eq1182525 (σ X0) X1
       grind)
    | exact resolve eq1182525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182525
  have eq1185919 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1183611 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq1183611
    | (have j0 := eq1183611 X0 X1
       grind)
    | exact resolve eq1183611 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1183611
  have eq1190202 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq543087 (σ X0) X1
       have i₂ := eq1185919 X0 X1
       grind)
    | exact superpose eq1185919 eq543087
    | (have j0 := eq543087 (σ X1) X0
       have j1 := eq1185919 X1 X0
       grind)
    | exact resolve eq543087 eq1185919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185919
  have eq1190440 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1190202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190202
  have eq1196705 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1190440 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1190440
    | (have j0 := eq1190440 (σ X0) X1
       grind)
    | exact resolve eq1190440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190440
  have eq1199175 : ∀ X0 X1 : G, (τ (τ (σ X0))) = (M.op (τ (τ (σ X0))) (τ X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq197466 (σ X0) X1
       have i₂ := eq1196705 X0 X1
       grind)
    | exact superpose eq1196705 eq197466
    | (have j1 := eq1196705 X0 X1
       grind)
    | exact resolve eq197466 eq1196705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197466 eq1196705
  have eq1200620 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1199175 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1199175
    | (have j0 := eq1199175 X0 X1
       grind)
    | exact resolve eq1199175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199175
  have eq1214908 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1154738 (τ X1) (τ X0)
       have i₂ := eq1200620 X0 X1
       grind)
    | exact superpose eq1200620 eq1154738
    | (have j0 := eq1154738 (τ X1) (τ X0)
       have j1 := eq1200620 X0 X1
       grind)
    | (have r₁ := eq1154738 (τ X1) (τ X0)
       have r₂ := eq1200620 X0 X1
       grind)
    | exact resolve eq1154738 eq1200620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154738 eq1200620
  have eq1214909 : ∀ X0 X1 : G, (τ X0) = (k (τ X1) (τ X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1214908 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214908
  have eq1214921 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1214909 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq1214909
    | (have j0 := eq1214909 X0 X1
       grind)
    | exact resolve eq1214909 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1214909
  have eq1219942 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1214921 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1214921
    | exact resolve eq1214921 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214921
  have eq1221300 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1219942 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1219942
    | (have j0 := eq1219942 X0 X1
       grind)
    | exact resolve eq1219942 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219942
  have eq1221371 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1221300 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1221300
    | (have j0 := eq1221300 X0 X1
       grind)
    | exact resolve eq1221300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221300
  have eq1229904 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1221371 y x
       grind)
    | exact superpose eq1221371 eq16
    | (have j1 := eq1221371 y x
       grind)
    | exact resolve eq16 eq1221371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221371
  have eq1231976 : x = (k y x) := by
    first
    | (have j1 := eq1175573 y x
       grind)
    | (have r₁ := eq1229904
       have r₂ := eq1175573 y x
       grind)
    | exact resolve eq1229904 eq1175573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175573 eq1229904
  have eq1236165 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq543087 y x
       have i₂ := eq1231976
       grind)
    | exact superpose eq1231976 eq543087
    | (have j0 := eq543087 y x
       grind)
    | exact resolve eq543087 eq1231976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543087 eq1231976
  have eq1236171 : x = (M.op x y) := by grind
  clear eq1236165
  have eq1236308 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq199800 y x
       have i₂ := eq1236171
       grind)
    | exact superpose eq1236171 eq199800
    | exact resolve eq199800 eq1236171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199800
  have eq1241230 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1236308
       grind)
    | exact superpose eq1236308 eq16
    | exact resolve eq16 eq1236308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236308
  have eq1241745 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1241230
       have i₂ := eq1236171
       grind)
    | exact superpose eq1236171 eq1241230
    | exact resolve eq1241230 eq1236171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236171 eq1241230
  have eq1241746 : False := by grind
  exact eq1241746

/-- `Equation4480`: `x ◇ (y ◇ y) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pxx_pxy_Equation4480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X1 : G, (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq66 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq24 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq24
    | exact resolve eq24 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq274 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq303 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq302 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq302
    | (have j0 := eq302 X0
       grind)
    | exact resolve eq302 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq366 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq303 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq721 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq273 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq273
    | (have j0 := eq273 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq273 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq273 (M.op X0 X0) X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq273
    | (have j0 := eq273 (M.op X0 X0) X0
       grind)
    | exact resolve eq273 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq273 X0 X1
       grind)
    | exact superpose eq273 eq10
    | (have j1 := eq273 X0 X1
       grind)
    | exact resolve eq10 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6408 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq64 (τ x)
       have i₂ := eq274 x x
       grind)
    | exact superpose eq274 eq64
    | (have j1 := eq274 X0 X0
       grind)
    | exact resolve eq64 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6412 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq274 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6413 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq6412 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6412
  have eq6415 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq6408 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6408
  have eq6427 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (τ (k (k X0 X0) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6415 X0
       have i₂ := eq33 X0 (k X0 X0)
       grind)
    | exact superpose eq33 eq6415
    | (have j0 := eq6415 X0
       grind)
    | exact resolve eq6415 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq6415
  have eq6450 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6413 (σ X0)
       have i₂ := eq30 X0 (σ X0)
       grind)
    | exact superpose eq30 eq6413
    | (have j0 := eq6413 (σ X0)
       grind)
    | exact resolve eq6413 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq6470 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6450 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6450
    | (have j0 := eq6450 X0
       grind)
    | exact resolve eq6450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6450
  have eq6487 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6470 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6470
    | (have j0 := eq6470 X0
       grind)
    | exact resolve eq6470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6470
  have eq6525 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6487 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6487
    | (have j0 := eq6487 (σ X0)
       grind)
    | exact resolve eq6487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6798 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ (k X0 X0)))) = (τ (k (σ (k X0 X0)) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6427 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6427
    | (have j0 := eq6427 (σ X0)
       grind)
    | exact resolve eq6427 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6821 : ∀ X0 : G, (M.op (τ (k X0 X0)) (M.op (τ X0) (τ X0))) = (M.op (τ (k (k X0 X0) X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (τ (k X0 X0)) (τ X0)
       have i₂ := eq6427 X0
       grind)
    | exact superpose eq6427 eq9
    | (have j1 := eq6427 X0
       grind)
    | exact resolve eq9 eq6427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6427
  have eq6842 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ (k X0 X0)))) = (k (τ (σ (k X0 X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6798 X0
       have i₂ := eq24 (σ (k X0 X0)) X0
       grind)
    | exact superpose eq24 eq6798
    | (have j0 := eq6798 X0
       grind)
    | exact resolve eq6798 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6798
  have eq6865 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (τ (σ X0)) (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6842 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq6842
    | (have j0 := eq6842 X0
       grind)
    | exact resolve eq6842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6842
  have eq6881 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6865 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6865
    | (have j0 := eq6865 X0
       grind)
    | exact resolve eq6865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865
  have eq6897 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6881 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6881
    | (have j0 := eq6881 X0
       grind)
    | exact resolve eq6881 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6881
  have eq6955 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6897 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6897
    | (have j0 := eq6897 (σ X0)
       grind)
    | exact resolve eq6897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6978 : ∀ X0 : G, (k (τ (k (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (k (σ X0) (σ X0)) X0
       have i₂ := eq6897 (σ X0)
       grind)
    | exact superpose eq6897 eq24
    | (have j1 := eq6897 (σ X0)
       grind)
    | exact resolve eq24 eq6897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7068 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = (τ (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6978 x
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6978
    | (have j0 := eq6978 X0
       grind)
    | exact resolve eq6978 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6978
  have eq7088 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6955 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq6955
    | (have j0 := eq6955 X0
       grind)
    | exact resolve eq6955 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6955
  have eq7133 : ∀ X0 : G, (k (k X0 X0) X0) = (τ (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7068 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq7068
    | (have j0 := eq7068 X0
       grind)
    | exact resolve eq7068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7068
  have eq7210 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7088 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq7088
    | (have j0 := eq7088 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq7088 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7088
  have eq7305 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7210 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7210
  have eq7336 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7305 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq7305
    | (have j0 := eq7305 X0
       grind)
    | exact resolve eq7305 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7305
  have eq7462 : ∀ X0 : G, (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7133 X0
       have i₂ := eq273 X0 X0
       grind)
    | exact superpose eq273 eq7133
    | (have j0 := eq7133 X0
       have j1 := eq273 X0 X0
       grind)
    | exact resolve eq7133 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7133
  have eq7542 : ∀ X0 : G, (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq7462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7462
  have eq7554 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7542 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq7542
    | (have j0 := eq7542 X0
       grind)
    | exact resolve eq7542 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq7542
  have eq7684 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (k (σ (τ (M.op (σ (τ X0)) (σ (τ X0))))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (τ (M.op (σ (τ X0)) (σ (τ X0))))
       have i₂ := eq7554 (τ X0)
       grind)
    | exact superpose eq7554 eq20
    | (have j1 := eq7554 (τ X0)
       grind)
    | exact resolve eq20 eq7554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7554
  have eq7749 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (k (M.op (σ (τ X0)) (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7684 X0
       have i₂ := eq11 (M.op (σ (τ X0)) (σ (τ X0)))
       grind)
    | exact superpose eq11 eq7684
    | (have j0 := eq7684 X0
       grind)
    | exact resolve eq7684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7684
  have eq7832 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (k (k (τ X0) (τ X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7749 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7749
    | (have j0 := eq7749 X0
       grind)
    | exact resolve eq7749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7749
  have eq7894 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7832 X0
       have i₂ := eq20 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq20 eq7832
    | (have j0 := eq7832 X0
       grind)
    | exact resolve eq7832 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7832
  have eq7954 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7894 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq7894
    | (have j0 := eq7894 X0
       grind)
    | exact resolve eq7894 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7894
  have eq7992 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7954 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7954
    | (have j0 := eq7954 X0
       grind)
    | exact resolve eq7954 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7954
  have eq8030 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7992 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq7992
    | (have j0 := eq7992 X0
       grind)
    | exact resolve eq7992 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7992
  have eq8059 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8030 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8030
    | (have j0 := eq8030 X0
       grind)
    | exact resolve eq8030 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8030
  have eq8092 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq8059 eq6897
    | (have j0 := eq6897 X0
       have j1 := eq8059 X0
       grind)
    | exact resolve eq6897 eq8059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6897
  have eq8117 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq8059 X0
       grind)
    | exact superpose eq8059 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq8059 X0
       grind)
    | exact resolve eq14 eq8059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8209 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq14 eq8117
    | (have j0 := eq8117 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq8117 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8117
  have eq8276 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq14 eq8209
    | (have j0 := eq8209 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq8209 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8209
  have eq8304 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (k X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0
       have i₂ := eq8092 X0
       grind)
    | exact superpose eq8092 eq9
    | (have j1 := eq8092 X0
       grind)
    | exact resolve eq9 eq8092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8092
  have eq8309 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (k X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8304 X0
       have i₂ := eq9 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq8304
    | (have j0 := eq8304 X0
       grind)
    | exact resolve eq8304 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8304
  have eq8329 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (k X0 X0) (k X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) (k X0 X0)
       have i₂ := eq8309 X0
       grind)
    | exact superpose eq8309 eq9
    | (have j1 := eq8309 X0
       grind)
    | exact resolve eq9 eq8309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8309
  have eq17455 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ (k X0 X0))) = (M.op (τ (k (k X0 X0) X0)) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6821 x
       have i₂ := eq274 x x
       grind)
    | exact superpose eq274 eq6821
    | (have j0 := eq6821 X0
       have j1 := eq274 X0 X0
       grind)
    | exact resolve eq6821 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq6821
  have eq17462 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ (k X0 X0))) = (M.op (τ (k (k X0 X0) X0)) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq17455 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17455
  have eq17466 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ (k X0 X0))) = (M.op (τ (k (k X0 X0) X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq17462 X0
       have j1 := eq6413 X0
       grind)
    | (have r₁ := eq17462 X0
       have r₂ := eq6413 X0
       grind)
    | exact resolve eq17462 eq6413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6413 eq17462
  have eq17708 : ∀ X0 : G, (M.op (τ (k (σ X0) (σ X0))) (τ (k (σ X0) (σ X0)))) = (M.op (τ (k (k (σ X0) (σ X0)) (σ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17466 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17466
    | exact resolve eq17466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17466
  have eq17745 : ∀ X0 : G, (M.op (τ (k (σ X0) (σ X0))) (τ (k (σ X0) (σ X0)))) = (M.op (k (τ (k (σ X0) (σ X0))) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17708 X0
       have i₂ := eq24 (k (σ X0) (σ X0)) X0
       grind)
    | exact superpose eq24 eq17708
    | (have j0 := eq17708 X0
       grind)
    | exact resolve eq17708 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17708
  have eq17767 : ∀ X0 : G, (M.op (k (τ (σ X0)) X0) (k (τ (σ X0)) X0)) = (M.op (k (k (τ (σ X0)) X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17745 x
       have i₂ := eq24 (σ x) x
       grind)
    | exact superpose eq24 eq17745
    | (have j0 := eq17745 X0
       grind)
    | exact resolve eq17745 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17745
  have eq17787 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = (M.op (k (k X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17767 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17767
    | (have j0 := eq17767 X0
       grind)
    | exact resolve eq17767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17767
  have eq17805 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq8059 eq17787
    | (have j0 := eq17787 X0
       have j1 := eq8059 X0
       grind)
    | exact resolve eq17787 eq8059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8059 eq17787
  have eq17821 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17805 X0
       have i₂ := eq9 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq17805
    | (have j0 := eq17805 X0
       grind)
    | exact resolve eq17805 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17805
  have eq17918 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (k X0 X0)) = (M.op (k X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) (k X0 X0)
       have i₂ := eq17821 X0
       grind)
    | exact superpose eq17821 eq9
    | (have j1 := eq17821 X0
       grind)
    | exact resolve eq9 eq17821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20088 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq17821 eq8329
    | (have j0 := eq8329 X0
       have j1 := eq17821 X0
       grind)
    | exact resolve eq8329 eq17821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8329
  have eq22310 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (k X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq20088 eq17918
    | (have j0 := eq17918 X0
       have j1 := eq20088 X0
       grind)
    | exact resolve eq17918 eq20088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17918 eq20088
  have eq22321 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22310
  have eq22331 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22321 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq22321
    | (have j0 := eq22321 X0
       grind)
    | exact resolve eq22321 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22321
  have eq23001 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17821 X0
       have i₂ := eq8276 X0
       grind)
    | exact superpose eq8276 eq17821
    | (have j0 := eq17821 X0
       have j1 := eq8276 X0
       grind)
    | exact resolve eq17821 eq8276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8276 eq17821
  have eq23026 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23001 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23001
  have eq23045 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq14 eq23026
    | (have j0 := eq23026 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq23026 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23026
  have eq23046 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23045 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23045
  have eq23125 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq22331 X0
       have i₂ := eq23046 X0
       grind)
    | exact superpose eq23046 eq22331
    | (have j0 := eq22331 X0
       have j1 := eq23046 X0
       grind)
    | exact resolve eq22331 eq23046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22331 eq23046
  have eq23135 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23125 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23125
  have eq23143 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq14 eq23135
    | (have j0 := eq23135 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq23135 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23135
  have eq23144 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23143 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23143
  have eq23156 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq14 eq23144
    | (have j0 := eq23144 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq23144 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23144
  have eq23167 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq23156 X0
       have j1 := eq6487 X0
       grind)
    | (have r₁ := eq23156 X0
       have r₂ := eq6487 X0
       grind)
    | exact resolve eq23156 eq6487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6487 eq23156
  have eq195276 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq721 x y
       grind)
    | exact superpose eq721 eq16
    | (have j1 := eq721 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq721 x y
       grind)
    | exact resolve eq16 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq195328 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq195276
  have eq195538 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq746 x x
       have i₂ := eq195328
       grind)
    | exact superpose eq195328 eq746
    | (have j0 := eq746 y x
       grind)
    | exact resolve eq746 eq195328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195541 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq195328
  have eq195564 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq195541
  have eq195567 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq195538
  have eq195583 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq195564
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq195564
    | exact resolve eq195564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195564
  have eq195586 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq195567
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq195567
    | exact resolve eq195567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195567
  have eq195622 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq195583
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq195583 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195583
  have eq195689 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64 (σ y)
       have i₂ := eq195622
       grind)
    | exact superpose eq195622 eq64
    | exact resolve eq64 eq195622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195709 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (σ y) (σ y)
       have i₂ := eq195622
       grind)
    | exact superpose eq195622 eq9
    | exact resolve eq9 eq195622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195622
  have eq195727 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq195689
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq195689
    | exact resolve eq195689 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195689
  have eq195768 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq195727
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq195727 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195727
  have eq196065 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq746 y y
       have i₂ := eq195586
       grind)
    | exact superpose eq195586 eq746
    | exact resolve eq746 eq195586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195586
  have eq196102 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq196065
  have eq196135 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq196102
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq196102
    | exact resolve eq196102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196102
  have eq196223 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq196135
       grind)
    | exact superpose eq196135 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq196135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196224 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq196223
  have eq196253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7336 x
       have i₂ := eq196224
       grind)
    | exact superpose eq196224 eq7336
    | (have j0 := eq7336 x
       grind)
    | exact resolve eq7336 eq196224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196261 : x ≠ y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  have eq196266 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq196253
       have r₂ := eq16
       grind)
    | exact resolve eq196253 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196253
  have eq196273 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq196266
       have r₂ := eq196261
       grind)
    | exact resolve eq196266 eq196261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196261 eq196266
  have eq196315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq195768 eq195709
    | exact resolve eq195709 eq195768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195709 eq195768
  have eq196316 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq196315
       have r₂ := eq16
       grind)
    | exact resolve eq196315 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196315
  have eq196317 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq196316
       grind)
    | exact superpose eq196316 eq10
    | exact resolve eq10 eq196316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196316
  have eq196531 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq196317
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq196317
    | exact resolve eq196317 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196317
  have eq196579 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq366 (σ x)
       have i₂ := eq196273
       grind)
    | exact superpose eq196273 eq366
    | exact resolve eq366 eq196273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196588 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq196579
       have r₂ := eq196273
       grind)
    | exact resolve eq196579 eq196273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196273 eq196579
  have eq196610 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq196588
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq196588
    | exact resolve eq196588 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196588
  have eq196631 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23167 eq196610
    | (have j1 := eq23167 x
       grind)
    | exact resolve eq196610 eq23167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196610
  have eq196653 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq196224 eq196631
    | exact resolve eq196631 eq196224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196224 eq196631
  have eq196654 : x = (k y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq196653
  have eq196718 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq196654 eq196135
    | exact resolve eq196135 eq196654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196135
  have eq196739 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq196654
       grind)
    | exact superpose eq196654 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq196654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196740 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq196739
  have eq196933 : y ≠ (M.op y y) ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq366 y
       have i₂ := eq196740
       grind)
    | exact superpose eq196740 eq366
    | exact resolve eq366 eq196740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196938 : x ≠ y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  have eq196943 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq196933
       have r₂ := eq196740
       grind)
    | exact resolve eq196933 eq196740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196740 eq196933
  have eq196953 : x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq196654 eq196943
    | exact resolve eq196943 eq196654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196654 eq196943
  have eq196960 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq196953
       have r₂ := eq196938
       grind)
    | exact resolve eq196953 eq196938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196938 eq196953
  have eq196968 : y = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  have eq196970 : (k x y) = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64 y
       have i₂ := eq196960
       grind)
    | exact superpose eq196960 eq64
    | exact resolve eq64 eq196960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196991 : (M.op x y) = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq196960
       grind)
    | exact superpose eq196960 eq9
    | exact resolve eq9 eq196960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196996 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq196991 eq196970
    | exact resolve eq196970 eq196991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196970 eq196991
  have eq197004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq273 x y
       have i₂ := eq196996
       grind)
    | exact superpose eq196996 eq273
    | (have j0 := eq273 x y
       grind)
    | exact resolve eq273 eq196996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197005 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq197004
       have r₂ := eq16
       grind)
    | exact resolve eq197004 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197004
  have eq197026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7336 x
       have i₂ := eq196968
       grind)
    | exact superpose eq196968 eq7336
    | (have j0 := eq7336 x
       grind)
    | exact resolve eq7336 eq196968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7336
  have eq197034 : x ≠ y ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  have eq197041 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq197026
       have r₂ := eq16
       grind)
    | exact resolve eq197026 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197026
  have eq197046 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq197005
  have eq197054 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq197041
       have r₂ := eq197034
       grind)
    | exact resolve eq197041 eq197034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197034 eq197041
  have eq197065 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq197046
  have eq197247 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq197065
  have eq197321 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq366 (σ x)
       have i₂ := eq197054
       grind)
    | exact superpose eq197054 eq366
    | exact resolve eq366 eq197054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197337 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq197321
       have r₂ := eq197054
       grind)
    | exact resolve eq197321 eq197054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197054 eq197321
  have eq197360 : (σ x) = (σ (k x x)) ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq197337
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq197337
    | exact resolve eq197337 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197337
  have eq197382 : (σ x) = (σ (M.op x x)) ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23167 eq197360
    | (have j1 := eq23167 x
       grind)
    | exact resolve eq197360 eq23167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197360
  have eq197406 : (σ x) = (σ y) ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq196968 eq197382
    | exact resolve eq197382 eq196968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196968 eq197382
  have eq197407 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq197406
  have eq197922 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq746 x x
       have i₂ := eq197247
       grind)
    | exact superpose eq197247 eq746
    | (have j0 := eq746 y x
       grind)
    | exact resolve eq746 eq197247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq197247
  have eq197965 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq197922
  have eq198001 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq197965
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq197965
    | exact resolve eq197965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197965
  have eq198046 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23167 eq198001
    | (have j1 := eq23167 x
       grind)
    | exact resolve eq198001 eq23167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23167 eq198001
  have eq198661 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 (σ y)
       have i₂ := eq198046
       grind)
    | exact superpose eq198046 eq64
    | exact resolve eq64 eq198046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198686 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (σ y) (σ y)
       have i₂ := eq198046
       grind)
    | exact superpose eq198046 eq9
    | exact resolve eq9 eq198046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198046
  have eq198729 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq198661
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq198661
    | exact resolve eq198661 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198661
  have eq198764 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq196996 eq198729
    | exact resolve eq198729 eq196996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196996 eq198729
  have eq199765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq198764 eq198686
    | exact resolve eq198686 eq198764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198686 eq198764
  have eq199766 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq199765
       have r₂ := eq16
       grind)
    | exact resolve eq199765 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199765
  have eq199770 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 x
       have i₂ := eq199766
       grind)
    | exact superpose eq199766 eq64
    | exact resolve eq64 eq199766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199796 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  have eq199814 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq197407 eq199770
    | exact resolve eq199770 eq197407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197407 eq199770
  have eq199835 : (M.op x x) = (M.op y (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq199814
       grind)
    | exact superpose eq199814 eq9
    | exact resolve eq9 eq199814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199814
  have eq199837 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq199766 eq199835
    | exact resolve eq199835 eq199766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199766 eq199835
  have eq199841 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq196960 eq199837
    | exact resolve eq199837 eq196960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196960 eq199837
  have eq199845 : x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq199841
       have r₂ := eq199796
       grind)
    | exact resolve eq199841 eq199796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199796 eq199841
  have eq199867 : x ≠ (M.op x x) ∨ x = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq366 x
       have i₂ := eq199845
       grind)
    | exact superpose eq199845 eq366
    | exact resolve eq366 eq199845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199869 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq723 x
       have i₂ := eq199845
       grind)
    | exact superpose eq199845 eq723
    | (have j0 := eq723 x
       grind)
    | exact resolve eq723 eq199845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq199875 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq199869
  have eq199879 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq199845 eq199875
    | exact resolve eq199875 eq199845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199875
  have eq199880 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq199879
  have eq199883 : x = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq199867
       have r₂ := eq199845
       grind)
    | exact resolve eq199867 eq199845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199845 eq199867
  have eq199902 : x = y ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq199883 eq196718
    | exact resolve eq196718 eq199883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196718 eq199883
  have eq199939 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq199902
  have eq200405 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq199939
       grind)
    | exact superpose eq199939 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq199939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200406 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq200405
  have eq200417 : (M.op y y) = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq64 y
       have i₂ := eq200406
       grind)
    | exact superpose eq200406 eq64
    | exact resolve eq64 eq200406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200406
  have eq200454 : x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq199939 eq200417
    | exact resolve eq200417 eq199939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199939 eq200417
  have eq200455 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq200454
  have eq200473 : (k x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq64 y
       have i₂ := eq200455
       grind)
    | exact superpose eq200455 eq64
    | exact resolve eq64 eq200455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200498 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq200455
       grind)
    | exact superpose eq200455 eq9
    | exact resolve eq9 eq200455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200455
  have eq200530 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq200498 eq200473
    | exact resolve eq200473 eq200498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200473 eq200498
  have eq200552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq273 x y
       have i₂ := eq200530
       grind)
    | exact superpose eq200530 eq273
    | (have j0 := eq273 x y
       grind)
    | exact resolve eq273 eq200530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq200553 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq200552
       have r₂ := eq16
       grind)
    | exact resolve eq200552 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200552
  have eq200554 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq199880 eq200553
    | exact resolve eq200553 eq199880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199880 eq200553
  have eq200555 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq200554
  have eq200611 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq64 (σ y)
       have i₂ := eq200555
       grind)
    | exact superpose eq200555 eq64
    | exact resolve eq64 eq200555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq200636 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9 (σ y) (σ y)
       have i₂ := eq200555
       grind)
    | exact superpose eq200555 eq9
    | exact resolve eq9 eq200555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200555
  have eq200685 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq200611
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq200611
    | exact resolve eq200611 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200611
  have eq200721 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq200530 eq200685
    | exact resolve eq200685 eq200530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200530 eq200685
  have eq200844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq200721 eq200636
    | exact resolve eq200636 eq200721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200636 eq200721
  have eq200845 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq200844
       have r₂ := eq16
       grind)
    | exact resolve eq200844 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200844
  have eq200848 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq200845
       grind)
    | exact superpose eq200845 eq10
    | exact resolve eq10 eq200845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200845
  have eq201066 : x = y ∨ x = y := by
    first
    | (have i₁ := eq200848
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq200848
    | exact resolve eq200848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200848
  have eq201067 : x = y := by grind
  clear eq201066
  have eq201068 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201067
       grind)
    | exact superpose eq201067 eq16
    | exact resolve eq16 eq201067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201072 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq196531
       have i₂ := eq201067
       grind)
    | exact superpose eq201067 eq196531
    | exact resolve eq196531 eq201067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196531
  have eq201077 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq201072
       have i₂ := eq201067
       grind)
    | exact superpose eq201067 eq201072
    | exact resolve eq201072 eq201067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201072
  have eq201078 : x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq201077
  have eq201087 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq201078
       have i₂ := eq201067
       grind)
    | exact superpose eq201067 eq201078
    | exact resolve eq201078 eq201067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201067 eq201078
  have eq201088 : x = (M.op x x) := by grind
  clear eq201087
  have eq201094 : x = (M.op x x) := by grind
  clear eq201088
  have eq201105 : x ≠ (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq366 x
       have i₂ := eq201094
       grind)
    | exact superpose eq201094 eq366
    | exact resolve eq366 eq201094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq201121 : x = (k x x) := by
    first
    | (have r₁ := eq201105
       have r₂ := eq201094
       grind)
    | exact resolve eq201105 eq201094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201105
  have eq201142 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6525 x
       have i₂ := eq201121
       grind)
    | exact superpose eq201121 eq6525
    | (have j0 := eq6525 x
       grind)
    | exact resolve eq6525 eq201121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6525 eq201121
  have eq201164 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq201142
  have eq201175 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq201164
  have eq201176 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq201068
       have i₂ := eq201094
       grind)
    | exact superpose eq201094 eq201068
    | exact resolve eq201068 eq201094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201068 eq201094
  have eq201177 : False := by grind
  exact eq201177

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pyx_pxy_Equation4494 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
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
  clear eq47
  have eq179 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op y y) (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) x
       have i₂ := eq179 (M.op x (M.op y y))
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq190 X0
       have i₂ := eq179 (M.op y y)
       grind)
    | exact superpose eq179 eq190
    | exact resolve eq190 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq190
  have eq202 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq180 eq202
    | exact resolve eq202 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq202
  have eq216 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq191 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) y)
       have r₂ := eq191 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq244 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq203 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq203 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq427 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq219 eq34
    | exact resolve eq34 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq219
  have eq457 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq427 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq427
    | exact resolve eq427 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq494 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq531 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq566 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ (k x y) = (M.op y x) := by
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
  have eq567 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq857 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq247 eq736
    | exact resolve eq736 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq736
  have eq891 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ x) (σ y)) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq857 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq857
    | exact resolve eq857 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq1757 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq494
       grind)
    | exact superpose eq494 eq40
    | exact resolve eq40 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1758 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1757
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1757
    | exact resolve eq1757 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1760 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1758
    | exact resolve eq1758 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq2169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1760 eq495
    | exact resolve eq495 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2176 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2169
       have r₂ := eq27
       grind)
    | exact resolve eq2169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169
  have eq2191 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2176 eq16
    | exact resolve eq16 eq2176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2194 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2176 eq2191
    | exact resolve eq2191 eq2176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176 eq2191
  have eq2267 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2194 eq891
    | exact resolve eq891 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq2194
  have eq2309 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq31 eq2267
    | exact resolve eq2267 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq2318 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2309 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq2309 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq2309 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309
  have eq2329 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq494
       have i₂ := eq2318 x
       grind)
    | exact superpose eq2318 eq494
    | exact resolve eq494 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2331 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq2318 y
       grind)
    | exact superpose eq2318 eq36
    | exact resolve eq36 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2318
  have eq2336 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2329
  have eq2345 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2331
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2331
    | exact resolve eq2331 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331
  have eq2364 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq2336
       grind)
    | exact superpose eq2336 eq16
    | exact resolve eq16 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2367 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2336 eq2364
    | exact resolve eq2364 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336 eq2364
  have eq2378 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2345 eq532
    | (have j0 := eq532 (σ y)
       grind)
    | (have r₁ := eq532 (σ y)
       have r₂ := eq2345
       grind)
    | exact resolve eq532 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345
  have eq2379 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2378
  have eq2454 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2367 x
       grind)
    | exact superpose eq2367 eq18
    | (have j1 := eq2367 x
       grind)
    | exact resolve eq18 eq2367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367
  have eq2524 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2454 eq27
    | exact resolve eq27 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2525 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2454 eq203
    | exact resolve eq203 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2608 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq2525
    | (have j0 := eq2525 X0
       grind)
    | exact resolve eq2525 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525
  have eq2650 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2454 eq2608
    | exact resolve eq2608 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2608
  have eq3031 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2379 eq16
    | exact resolve eq16 eq2379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3042 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2379 eq3031
    | exact resolve eq3031 eq2379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379 eq3031
  have eq3076 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3042 eq26
    | (have j1 := eq3042 (σ x)
       grind)
    | exact resolve eq26 eq3042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042
  have eq3152 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3076 eq27
    | exact resolve eq27 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3076
  have eq4157 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2454 eq567
    | (have r₁ := eq567
       have r₂ := eq2454
       grind)
    | exact resolve eq567 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454
  have eq4158 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4157
  have eq4159 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2650 eq4158
    | exact resolve eq4158 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650 eq4158
  have eq4161 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq4159
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq4159 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4159
  have eq4164 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4161 eq1760
    | exact resolve eq1760 eq4161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760 eq4161
  have eq4172 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq4164
  have eq4179 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4172
       have r₂ := eq2524
       grind)
    | exact resolve eq4172 eq2524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524 eq4172
  have eq4206 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq4179
       grind)
    | exact superpose eq4179 eq16
    | exact resolve eq16 eq4179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4221 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4179 eq4206
    | exact resolve eq4206 eq4179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4179 eq4206
  have eq4293 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4221 x
       grind)
    | exact superpose eq4221 eq18
    | (have j1 := eq4221 x
       grind)
    | exact resolve eq18 eq4221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4221
  have eq4337 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4293
  have eq4365 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4337
       grind)
    | exact superpose eq4337 eq24
    | exact resolve eq24 eq4337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4379 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) (M.op x y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq457 X0
       have i₂ := eq4337
       grind)
    | exact superpose eq4337 eq457
    | exact resolve eq457 eq4337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq4380 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq494
       have i₂ := eq4337
       grind)
    | exact superpose eq4337 eq494
    | exact resolve eq494 eq4337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq4337
  have eq4436 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq4380
  have eq4440 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4365
    | exact resolve eq4365 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq4462 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4440 eq3152
    | (have r₁ := eq3152
       have r₂ := eq4440
       grind)
    | exact resolve eq3152 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq4471 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4462
  have eq4472 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4471
  have eq4485 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4472 eq27
    | exact resolve eq27 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4486 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4472 eq203
    | exact resolve eq203 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq4499 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4472 eq567
    | (have r₁ := eq567
       have r₂ := eq4472
       grind)
    | exact resolve eq567 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq4529 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4499
  have eq4572 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq4486
    | (have j0 := eq4486 X0
       grind)
    | exact resolve eq4486 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4486
  have eq4614 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4472 eq4572
    | exact resolve eq4572 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4572
  have eq4726 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4440 eq4485
    | exact resolve eq4485 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485
  have eq4727 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq4726
  have eq8841 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4436 eq35
    | exact resolve eq35 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4436
  have eq8851 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq8841
    | exact resolve eq8841 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8841
  have eq8853 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4440 eq8851
    | exact resolve eq8851 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8851
  have eq11737 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4529 eq4614
    | exact resolve eq4614 eq4529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4529 eq4614
  have eq11749 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq11737
  have eq11758 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq11749
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq11749 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11749
  have eq11769 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11758 eq8853
    | exact resolve eq8853 eq11758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8853 eq11758
  have eq11780 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq11769
  have eq11790 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11780
       have r₂ := eq4727
       grind)
    | exact resolve eq11780 eq4727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11780
  have eq11804 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11790 eq4379
    | exact resolve eq4379 eq11790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4379 eq11790
  have eq11842 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq11804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11804
  have eq11852 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq11842
    | (have j0 := eq11842 X0
       grind)
    | exact resolve eq11842 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11842
  have eq11858 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4440 eq11852
    | exact resolve eq11852 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4440 eq11852
  have eq12785 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11858 eq532
    | (have j0 := eq532 (σ y)
       grind)
    | (have r₁ := eq532 (σ y)
       have r₂ := eq11858 (σ y)
       grind)
    | exact resolve eq532 eq11858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq11858
  have eq12812 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12785
  have eq12865 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12812 eq16
    | exact resolve eq16 eq12812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12884 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12812 eq12865
    | exact resolve eq12865 eq12812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12812 eq12865
  have eq12942 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12884 eq26
    | (have j1 := eq12884 (σ x)
       grind)
    | exact resolve eq26 eq12884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12884
  have eq13013 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4472 eq12942
    | exact resolve eq12942 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4472 eq12942
  have eq13049 : x = (M.op x y) := by
    first
    | (have r₁ := eq13013
       have r₂ := eq4727
       grind)
    | exact resolve eq13013 eq4727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4727 eq13013
  have eq13056 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13049
       grind)
    | exact superpose eq13049 eq18
    | exact resolve eq18 eq13049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq13057 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq13049
       grind)
    | exact superpose eq13049 eq22
    | exact resolve eq22 eq13049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq13062 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (k (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq566
       have i₂ := eq13049
       grind)
    | exact superpose eq13049 eq566
    | (have r₁ := eq566
       have r₂ := eq13049
       grind)
    | exact resolve eq566 eq13049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq13049
  have eq13071 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ y = (M.op y y) := by grind
  clear eq13062
  have eq13073 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13057 eq20
    | exact resolve eq20 eq13057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13169 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq13056 eq191
    | exact resolve eq191 eq13056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq18959 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq13071 eq13169
    | exact resolve eq13169 eq13071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13071 eq13169
  have eq18980 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have j1 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq18959
       have r₂ := eq13 x y
       grind)
    | exact resolve eq18959 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18959
  have eq19006 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18980 eq40
    | exact resolve eq40 eq18980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq18980
  have eq19010 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq19006
    | exact resolve eq19006 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19006
  have eq19013 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq13073 eq19010
    | exact resolve eq19010 eq13073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19010
  have eq19022 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19013 eq495
    | exact resolve eq495 eq19013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq19013
  have eq19031 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19022
  have eq19057 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19031 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq19031
       grind)
    | exact resolve eq13 eq19031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19067 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19031 eq16
    | exact resolve eq16 eq19031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19078 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19057 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19057
  have eq19088 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19031 eq19067
    | exact resolve eq19067 eq19031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19031 eq19067
  have eq19121 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19078 eq107
    | exact resolve eq107 eq19078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq19078
  have eq19130 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq19121
    | exact resolve eq19121 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq19121
  have eq19219 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19088 eq26
    | (have j1 := eq19088 (σ x)
       grind)
    | exact resolve eq26 eq19088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq19088
  have eq19363 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19219
  have eq19447 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq530 y y
       have i₂ := eq19130
       grind)
    | exact superpose eq19130 eq530
    | (have j0 := eq530 y y
       grind)
    | (have r₁ := eq530 y y
       have r₂ := eq19130
       grind)
    | exact resolve eq530 eq19130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq19130
  have eq19448 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19447
  have eq19449 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19448
  have eq19529 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq19449
       grind)
    | exact superpose eq19449 eq16
    | exact resolve eq16 eq19449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19550 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19449 eq19529
    | exact resolve eq19529 eq19449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19449 eq19529
  have eq19663 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13056
       have i₂ := eq19550 sF0
       grind)
    | exact superpose eq19550 eq13056
    | (have j1 := eq19550 x
       grind)
    | exact resolve eq13056 eq19550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13056 eq19550
  have eq19729 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19663 eq27
    | exact resolve eq27 eq19663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19663
  have eq19817 : y = (M.op x y) := by
    first
    | (have r₁ := eq19729
       have r₂ := eq13073
       grind)
    | exact resolve eq19729 eq13073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19729
  have eq19861 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq19817
       grind)
    | exact superpose eq19817 eq24
    | exact resolve eq24 eq19817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19817
  have eq19981 : (σ x) = (σ y) := by
    first
    | exact superpose eq13057 eq19861
    | exact resolve eq19861 eq13057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13057 eq19861
  have eq20129 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19981 eq19363
    | (have r₁ := eq19363
       have r₂ := eq19981
       grind)
    | exact resolve eq19363 eq19981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19363 eq19981
  have eq20130 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20129
  have eq20249 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq20130 eq27
    | exact resolve eq27 eq20130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20130
  have eq20337 : False := by grind
  exact eq20337

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyx_pyy_pyx_Equation450 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq12
    | (have r₁ := eq12 X0 (M.op X1 X0)
       have r₂ := eq22 X0 X1
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq188 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 x y
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) (σ X0)
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq22
    | (have j1 := eq48 X1 X0
       grind)
    | exact resolve eq22 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq923 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (M.op (σ X1) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq200 (M.op X0 X1) X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq200
    | (have j0 := eq200 (M.op X0 X1) X1
       grind)
    | exact resolve eq200 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq950 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq923 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq1235 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq188
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq188 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq1236 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1235
  have eq1371 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq193 (τ X1) (τ X0)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq193
    | (have j0 := eq193 (τ X0) (τ X1)
       grind)
    | exact resolve eq193 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq193
  have eq1429 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1371 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1371
    | (have j0 := eq1371 X0 X1
       grind)
    | exact resolve eq1371 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1436 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1429 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1429
    | (have j0 := eq1429 X0 X1
       grind)
    | exact resolve eq1429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1439 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1436 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1436
    | (have j0 := eq1436 X0 X1
       grind)
    | exact resolve eq1436 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436
  have eq1440 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1439 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1439
    | (have j0 := eq1439 X0 X1
       grind)
    | exact resolve eq1439 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1441 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1440 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1440
    | (have j0 := eq1440 X0 X1
       grind)
    | exact resolve eq1440 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq1442 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1441 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1441
    | (have j0 := eq1441 X0 X1
       grind)
    | exact resolve eq1441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq16604 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq950 x y
       have i₂ := eq1236
       grind)
    | exact superpose eq1236 eq950
    | exact resolve eq950 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq16626 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16604
  have eq16663 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq950 y y
       have i₂ := eq16626
       grind)
    | exact superpose eq16626 eq950
    | exact resolve eq950 eq16626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950 eq16626
  have eq16685 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq16663
  have eq16687 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16685
       grind)
    | exact superpose eq16685 eq16
    | exact resolve eq16 eq16685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16698 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq33 (σ x) (σ y)
       have i₂ := eq16685
       grind)
    | exact superpose eq16685 eq33
    | exact resolve eq33 eq16685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16685
  have eq16749 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16698
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16698
    | exact resolve eq16698 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16698
  have eq17143 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq33 (σ y) (σ y)
       have i₂ := eq16749
       grind)
    | exact superpose eq16749 eq33
    | exact resolve eq33 eq16749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq16749
  have eq17198 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq17143
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17143
    | exact resolve eq17143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17143
  have eq17199 : (σ x) = (σ (k y x)) := by grind
  clear eq17198
  have eq17216 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq17199
       grind)
    | exact superpose eq17199 eq10
    | exact resolve eq10 eq17199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17199
  have eq17297 : x = (k y x) := by
    first
    | (have i₁ := eq17216
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17216
    | exact resolve eq17216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17216
  have eq17464 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1442 y x
       have i₂ := eq17297
       grind)
    | exact superpose eq17297 eq1442
    | (have j0 := eq1442 y x
       grind)
    | exact resolve eq1442 eq17297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442 eq17297
  have eq17471 : x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq17464
  have eq17477 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16687
       have i₂ := eq17471
       grind)
    | exact superpose eq17471 eq16687
    | exact resolve eq16687 eq17471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17533 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq17477
  have eq18636 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq17533
       grind)
    | exact superpose eq17533 eq22
    | exact resolve eq22 eq17533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17533
  have eq18687 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16687
       have i₂ := eq18636
       grind)
    | exact superpose eq18636 eq16687
    | exact resolve eq16687 eq18636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16687 eq18636
  have eq18744 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq18687
  have eq18745 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq18744
  have eq19094 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22 (σ y) (σ y)
       have i₂ := eq18745
       grind)
    | exact superpose eq18745 eq22
    | exact resolve eq22 eq18745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18745
  have eq19607 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19094
       grind)
    | exact superpose eq19094 eq16
    | exact resolve eq16 eq19094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19094
  have eq19830 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19607
       have i₂ := eq17471
       grind)
    | exact superpose eq17471 eq19607
    | exact resolve eq19607 eq17471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17471
  have eq19833 : x = (M.op y y) := by grind
  clear eq19830
  have eq19842 : x = (M.op x y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq19833
       grind)
    | exact superpose eq19833 eq22
    | exact resolve eq22 eq19833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19833
  have eq20060 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq19607
       have i₂ := eq19842
       grind)
    | exact superpose eq19842 eq19607
    | exact resolve eq19607 eq19842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19607 eq19842
  have eq20120 : False := by grind
  exact eq20120
