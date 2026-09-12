import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1489`: `x = (y ◇ x) ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation1489 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1489 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1489.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X0 X1))) = X0 := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X1)) (M.op X1 X0)
       have i₂ := eq14 X0 X1
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
  clear eq36
  have eq75 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq75 y x
       grind)
    | exact superpose eq75 eq72
    | (have j1 := eq75 y x
       grind)
    | exact resolve eq72 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq113 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq114 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq116 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq116 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq43
    | exact resolve eq43 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq127 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq120
    | exact resolve eq120 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq120
  have eq813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq105 eq75
    | (have j0 := eq75 (σ y) (σ x)
       grind)
    | exact resolve eq75 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq813
    | exact resolve eq813 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq817 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq814
       have r₂ := eq27
       grind)
    | exact resolve eq814 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq819 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq817
    | exact resolve eq817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq822 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq819 eq114
    | (have r₁ := eq114
       have r₂ := eq819
       grind)
    | exact resolve eq114 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq825 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq819 eq14
    | exact resolve eq14 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq835 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq822
  have eq968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq835 eq105
    | exact resolve eq105 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq968
  have eq973 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq971
       have r₂ := eq27
       grind)
    | exact resolve eq971 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq998 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq973
       grind)
    | exact superpose eq973 eq113
    | (have r₁ := eq113
       have r₂ := eq973
       grind)
    | exact resolve eq113 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq973
       grind)
    | exact superpose eq973 eq127
    | exact resolve eq127 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq973
       grind)
    | exact superpose eq973 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1012 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq998
  have eq1014 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq999
    | exact resolve eq999 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1220 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq72
    | exact resolve eq72 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1222 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1220
    | exact resolve eq1220 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1222 eq75
    | (have j0 := eq75 (σ y) (σ x)
       grind)
    | exact resolve eq75 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1279
    | exact resolve eq1279 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq1285 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1282
       have r₂ := eq27
       grind)
    | exact resolve eq1282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1287 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1285
    | exact resolve eq1285 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1287 eq1014
    | exact resolve eq1014 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1290
  have eq1312 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1309
       have r₂ := eq27
       grind)
    | exact resolve eq1309 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq1512 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1010 X0
       grind)
    | (have r₁ := eq1010 X0
       have r₂ := eq1312
       grind)
    | exact resolve eq1010 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010 eq1312
  have eq1573 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1512 y
       grind)
    | exact superpose eq1512 eq72
    | exact resolve eq72 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1592 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1573
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1573
    | exact resolve eq1573 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1573
  have eq1594 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1592
    | exact resolve eq1592 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq1599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1594 eq75
    | (have j0 := eq75 (σ y) (σ x)
       grind)
    | exact resolve eq75 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1599
    | exact resolve eq1599 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq1605 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1602
       have r₂ := eq27
       grind)
    | exact resolve eq1602 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1607 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1605
    | exact resolve eq1605 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605
  have eq1672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1607 eq1014
    | exact resolve eq1014 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq1607
  have eq1691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1672
  have eq1694 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1691
       have r₂ := eq27
       grind)
    | exact resolve eq1691 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1696 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1694 eq27
    | exact resolve eq27 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1699 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1694 eq825
    | exact resolve eq825 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq1694
  have eq2253 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ x))))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1699 eq52
    | exact resolve eq52 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1699
  have eq2266 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2253
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq2253
    | exact resolve eq2253 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq2286 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2266 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq2266
       grind)
    | exact resolve eq13 eq2266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq2287 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq2286 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq2575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2287 eq105
    | exact resolve eq105 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq2287
  have eq2587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq2575
  have eq2595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq2587
    | exact resolve eq2587 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq2599 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2595
       have r₂ := eq27
       grind)
    | exact resolve eq2595 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595
  have eq2667 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq2599
       grind)
    | exact superpose eq2599 eq113
    | (have r₁ := eq113
       have r₂ := eq2599
       grind)
    | exact resolve eq113 eq2599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq2668 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq2599
       grind)
    | exact superpose eq2599 eq127
    | exact resolve eq127 eq2599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq2599
  have eq2681 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq2667
  have eq2683 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq2668
    | exact resolve eq2668 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq2834 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq2681
       grind)
    | exact superpose eq2681 eq72
    | exact resolve eq72 eq2681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2681
  have eq2837 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2834
    | exact resolve eq2834 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2834
  have eq2851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2837 eq75
    | (have j0 := eq75 (σ y) (σ x)
       grind)
    | exact resolve eq75 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq2837
  have eq2852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2851
    | exact resolve eq2851 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2851
  have eq2855 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2852
       have r₂ := eq27
       grind)
    | exact resolve eq2852 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq2857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2683 eq2855
    | exact resolve eq2855 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683 eq2855
  have eq2859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2857
    | exact resolve eq2857 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2857
  have eq2861 : x = (M.op x y) := by
    first
    | (have r₁ := eq2859
       have r₂ := eq27
       grind)
    | exact resolve eq2859 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2859
  have eq2863 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2861 eq20
    | exact resolve eq20 eq2861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2861
  have eq2905 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2863
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2863
    | exact resolve eq2863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2863
  have eq2911 : False := by grind
  exact eq2911

/-- `Equation1489`: `x = (y ◇ x) ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation1489 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1489 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1489.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  clear eq18
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
  clear eq23
  have eq69 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq106 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq122 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq107 (σ X0)
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq122 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq122
    | exact resolve eq122 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq122
  have eq219 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = X0 := by
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
  clear eq29
  have eq1297 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq219
    | (have j0 := eq219 X1 X1
       grind)
    | exact resolve eq219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq1320 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1297 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq1297
    | (have j0 := eq1297 (M.op X1 X1) X1
       grind)
    | exact resolve eq1297 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1297
  have eq1328 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X2 ∨ (τ (k X2 X0)) = (τ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq1320 X2 X0
       grind)
    | exact superpose eq1320 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq1320 (M.op X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq1320 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq1320 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq1320 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1359 : ∀ X0 X1 X2 : G, (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ X0 = X2 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1328 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1973 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq1359 X0 X2 X1
       grind)
    | exact superpose eq1359 eq11
    | (have j1 := eq1359 X0 X2 X1
       grind)
    | exact resolve eq11 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq1993 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1973 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq1973
    | (have j0 := eq1973 X0 X1 X1
       grind)
    | exact resolve eq1973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq2028 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1993 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993
  have eq2029 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2028 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq2153 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq2029 X1 (τ X0)
       grind)
    | exact superpose eq2029 eq19
    | (have j1 := eq2029 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2156 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2029 (σ X1) (σ X0)
       grind)
    | exact superpose eq2029 eq15
    | (have j1 := eq2029 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029
  have eq2283 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2153 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2153
    | exact resolve eq2153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq2364 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2283 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2283
    | (have j0 := eq2283 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq2283 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283
  have eq2640 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2156 x y
       grind)
    | exact superpose eq2156 eq16
    | (have j1 := eq2156 x y
       grind)
    | exact resolve eq16 eq2156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156
  have eq2669 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2640
       have i₂ := eq2364 x y
       grind)
    | exact superpose eq2364 eq2640
    | (have j1 := eq2364 (σ x) (σ y)
       grind)
    | (have r₁ := eq2640
       have r₂ := eq2364 x y
       grind)
    | (have r₁ := eq2640
       have r₂ := eq2364 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2640
       have r₂ := eq2364 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2640 eq2364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2364 eq2640
  have eq2670 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq2669
  have eq2674 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2670
       grind)
    | exact superpose eq2670 eq16
    | exact resolve eq16 eq2670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670
  have eq2675 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq2674
       have r₂ := eq133 x
       grind)
    | exact resolve eq2674 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674
  have eq2676 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2675
       grind)
    | exact superpose eq2675 eq16
    | exact resolve eq16 eq2675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2677 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2675
       grind)
    | exact superpose eq2675 eq10
    | exact resolve eq10 eq2675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2675
  have eq2733 : x = y := by
    first
    | (have i₁ := eq2677
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2677
    | exact resolve eq2677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2677
  have eq2734 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2676
       have i₂ := eq133 x
       grind)
    | exact superpose eq133 eq2676
    | exact resolve eq2676 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq2676
  have eq2740 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2734
       have i₂ := eq2733
       grind)
    | exact superpose eq2733 eq2734
    | exact resolve eq2734 eq2733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733 eq2734
  have eq2741 : False := by grind
  exact eq2741

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq47 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq73 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq117
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq117 eq16
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq163 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq155
  have eq210 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq47 (M.op y y)
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq48 (M.op sF3 sF3)
       have i₂ := eq14 sF3 sF3 sF3
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ y) X0)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq53 X0 X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq53 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq444 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq49 y X1 X0
       grind)
    | exact superpose eq49 eq47
    | exact resolve eq47 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq49 sF3 x x
       grind)
    | exact superpose eq49 eq48
    | exact resolve eq48 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq766 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq767 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X0)) X0) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3)) X1 X2 X0
       have i₂ := eq49 X0 X2 X3
       grind)
    | exact superpose eq49 eq52
    | exact resolve eq52 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq776 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq785 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq53 (M.op (M.op X0 (M.op X0 X0)) X0) x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X0 (M.op X1 X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 (M.op X1 X0)) X0) (M.op x (M.op x X1))
       have i₂ := eq52 X0 x x X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq822 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq229 sF4
       have i₂ := eq53 sF4 sF3
       grind)
    | exact superpose eq53 eq229
    | exact resolve eq229 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq872 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq72 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq72 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq72 X0 X0
       grind)
    | exact resolve eq12 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq882 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq872 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq885 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq882 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq882 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq882 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq882 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq896 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq885 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq885
    | (have j0 := eq885 X0 X1
       grind)
    | exact resolve eq885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq1305 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq241 X0 x x
       grind)
    | exact superpose eq241 eq53
    | exact resolve eq53 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1308 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1305 X0
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq1305
    | exact resolve eq1305 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq3538 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq766 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1308 sF0
       grind)
    | exact superpose eq1308 eq766
    | exact resolve eq766 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3561 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq3538
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq3538
    | exact resolve eq3538 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq3563 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3561 eq766
    | exact resolve eq766 eq3561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq3561
  have eq3584 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3563 eq14
    | exact resolve eq14 eq3563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563
  have eq3611 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq767 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1308 sF4
       grind)
    | exact superpose eq1308 eq767
    | exact resolve eq767 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3634 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3611
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3611
    | exact resolve eq3611 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3611
  have eq3651 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3634 eq767
    | exact resolve eq767 eq3634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3725 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3584 eq47
    | exact resolve eq47 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq3584
  have eq3754 : (M.op x y) = (k (M.op y (M.op x y)) (M.op x y)) := by grind
  have eq3877 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq822 eq219
    | exact resolve eq219 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq822
  have eq3906 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3877 X0
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3877
    | exact resolve eq3877 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3877
  have eq3907 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3906 x
       have i₂ := eq53 sF4 x
       grind)
    | exact superpose eq53 eq3906
    | exact resolve eq3906 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3906
  have eq3908 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3634 eq3907
    | exact resolve eq3907 eq3634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3634 eq3907
  have eq3909 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3908 eq3651
    | exact resolve eq3651 eq3908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3651
  have eq5111 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq444 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq241 X0 x X2
       grind)
    | exact superpose eq241 eq444
    | exact resolve eq444 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq5204 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq5111 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq5111
    | exact resolve eq5111 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq5214 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5204 X0 x
       have i₂ := eq53 X0 x
       grind)
    | exact superpose eq53 eq5204
    | exact resolve eq5204 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5204
  have eq6937 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq776 X0 X1 X2 X3
       have i₂ := eq5214 X0
       grind)
    | exact superpose eq5214 eq776
    | exact resolve eq776 eq5214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq7037 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6937 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq241 X0 x x
       grind)
    | exact superpose eq241 eq6937
    | exact resolve eq6937 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6937
  have eq7250 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7037 X0 X1 X2
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq7037
    | exact resolve eq7037 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7037
  have eq7285 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7250 X0 X1 X2
       have i₂ := eq5214 X0
       grind)
    | exact superpose eq5214 eq7250
    | exact resolve eq7250 eq5214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214 eq7250
  have eq7354 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq7285
    | (have j0 := eq7285 (σ y) X0 (σ x)
       grind)
    | exact resolve eq7285 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7433 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq767 X0
       have i₂ := eq7285 X0 X0 sF4
       grind)
    | exact superpose eq7285 eq767
    | exact resolve eq767 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq7631 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq785 X0
       have i₂ := eq7285 X0 X0 X0
       grind)
    | exact superpose eq7285 eq785
    | exact resolve eq785 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq7658 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    grind
  have eq8321 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq327
    | exact resolve eq327 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq8426 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8321 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq8321
    | (have j0 := eq8321 X0 X1
       grind)
    | exact resolve eq8321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8321
  have eq9076 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (k (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq73 eq12
    | (have j0 := eq12 (σ x) (σ X0)
       have j1 := eq73 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ X0)
       have r₂ := eq73 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq73 x
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq9092 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (k (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq9076 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9076
  have eq9096 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9092 X0
       have j1 := eq12 (σ x) (σ X0)
       grind)
    | (have r₁ := eq9092 x
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq9092 X0
       have r₂ := eq12 (σ x) (σ X0)
       grind)
    | exact resolve eq9092 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9092
  have eq9116 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ x) = (σ (k x X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq9096
    | (have j0 := eq9096 X0
       grind)
    | exact resolve eq9096 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq9096
  have eq9339 : ∀ X0 : G, (σ X0) ≠ (σ (k (M.op x y) X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq118 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ X0)
       have j1 := eq118 X0
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ X0)
       have r₂ := eq118 X0
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq118 (M.op x y)
       grind)
    | exact resolve eq12 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9354 : ∀ X0 : G, (σ X0) ≠ (σ (k (M.op x y) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq118 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq9355 : ∀ X0 : G, (σ X0) ≠ (σ (k (M.op x y) X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq9339 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9339
  have eq9359 : ∀ X0 : G, (σ X0) ≠ (σ (k (M.op x y) X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9355 X0
       have j1 := eq12 (σ (M.op x y)) (σ X0)
       grind)
    | (have r₁ := eq9355 (M.op x y)
       have r₂ := eq12 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq9355 X0
       have r₂ := eq12 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq9355 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9355
  have eq9378 : ∀ X0 : G, (σ X0) ≠ (σ (k (M.op x y) X0)) ∨ (σ (M.op x y)) = (σ (k (M.op x y) X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq38 eq9359
    | (have j0 := eq9359 X0
       grind)
    | exact resolve eq9359 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq9359
  have eq9442 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq240 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq9457 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9442 X0
       have i₂ := eq7631 X0
       grind)
    | exact superpose eq7631 eq9442
    | (have j0 := eq9442 X0
       grind)
    | exact resolve eq9442 eq7631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9442
  have eq9545 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0 X1
       have i₂ := eq7285 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq7285 eq452
    | exact resolve eq452 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq9574 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 y x X0
       have i₂ := eq9545 X0 x
       grind)
    | exact superpose eq9545 eq49
    | exact resolve eq49 eq9545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9545
  have eq9705 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq9574 (M.op X0 (M.op X0 X0))
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq9574
    | exact resolve eq9574 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9574
  have eq9822 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1308 X0
       have i₂ := eq9705 X0
       grind)
    | exact superpose eq9705 eq1308
    | exact resolve eq1308 eq9705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9842 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7433 sF4
       have i₂ := eq9705 sF4
       grind)
    | exact superpose eq9705 eq7433
    | exact resolve eq7433 eq9705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7433
  have eq9906 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9705 eq14
    | exact resolve eq14 eq9705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9705
  have eq9930 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9906 X0 X1
       have i₂ := eq14 X0 sF0 X0
       grind)
    | exact superpose eq14 eq9906
    | exact resolve eq9906 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9906
  have eq9964 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3908 eq9842
    | exact resolve eq9842 eq3908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908 eq9842
  have eq10038 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X1
       have i₂ := eq7285 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq7285 eq453
    | exact resolve eq453 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq10301 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq10038 eq49
    | exact resolve eq49 eq10038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10038
  have eq10446 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq10301 (M.op X0 (M.op X0 X0))
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq10301
    | exact resolve eq10301 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10301
  have eq10831 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq10446 eq14
    | exact resolve eq14 eq10446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10446
  have eq10855 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10831 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq10831
    | exact resolve eq10831 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10831
  have eq11473 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq10855 eq775
    | exact resolve eq775 eq10855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq10855
  have eq11474 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3909 eq11473
    | exact resolve eq11473 eq3909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3909 eq11473
  have eq11475 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7354 eq11474
    | exact resolve eq11474 eq7354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7354 eq11474
  have eq11504 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq11475 (M.op x (M.op x x)) x sF2
       have i₂ := eq49 x x sF2
       grind)
    | exact superpose eq49 eq11475
    | exact resolve eq11475 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq11475
  have eq13271 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq9964 eq11504
    | exact resolve eq11504 eq9964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9964 eq11504
  have eq18922 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq796 X0 x
       have i₂ := eq7285 X0 X0 x
       grind)
    | exact superpose eq7285 eq796
    | exact resolve eq796 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq18923 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18922 X0 X1
       have i₂ := eq7631 X0
       grind)
    | exact superpose eq7631 eq18922
    | exact resolve eq18922 eq7631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18922
  have eq23779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23779
    | exact resolve eq23779 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23779
  have eq23797 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23786
       have r₂ := eq28
       grind)
    | exact resolve eq23786 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23786
  have eq23799 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23797
    | exact resolve eq23797 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23797
  have eq24525 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq23799
  have eq24624 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24525 eq98
    | exact resolve eq98 eq24525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24625 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24525 eq101
    | exact resolve eq101 eq24525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24525
  have eq24642 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24625
  have eq24651 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq24624
    | exact resolve eq24624 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24624
  have eq24692 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq241 x x x
       have i₂ := eq24642
       grind)
    | exact superpose eq24642 eq241
    | exact resolve eq241 eq24642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24642
  have eq24724 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24692 x
       have i₂ := eq9930 (M.op x y) x
       grind)
    | (have i₁ := eq24692 x
       have i₂ := eq9930 (M.op x y) x
       grind)
    | exact superpose eq9930 eq24692
    | (have j0 := eq24692 x
       grind)
    | exact resolve eq24692 eq9930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24692
  have eq24744 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24724
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24724
    | exact resolve eq24724 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24724
  have eq24749 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3725 eq24744
    | exact resolve eq24744 eq3725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24744
  have eq25675 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24749 eq3754
    | exact resolve eq3754 eq24749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754 eq24749
  have eq26558 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25675 eq896
    | (have j0 := eq896 x (M.op x y)
       grind)
    | exact resolve eq896 eq25675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq25675
  have eq26559 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26558
  have eq26563 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq26559
    | exact resolve eq26559 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26559
  have eq26578 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26563
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26563
    | exact resolve eq26563 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26563
  have eq26579 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26578
  have eq26585 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq26579
    | exact resolve eq26579 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26579
  have eq26591 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26585
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26585
    | exact resolve eq26585 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26585
  have eq27903 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26591 eq1308
    | exact resolve eq1308 eq26591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq27907 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26591 eq7631
    | exact resolve eq7631 eq26591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26591
  have eq28757 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq771 X0 X1 X2 X3 X4
       have i₂ := eq7285 X0 X0 (M.op X1 (M.op X2 X1))
       grind)
    | exact superpose eq7285 eq771
    | exact resolve eq771 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq29309 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28757 (M.op X0 X0) X0 x X1 X2
       have i₂ := eq18923 X0 x
       grind)
    | exact superpose eq18923 eq28757
    | exact resolve eq28757 eq18923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18923 eq28757
  have eq29550 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29309 X0 X1 X2
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq29309
    | exact resolve eq29309 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29309
  have eq29792 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29550 X0 X1 X2
       have i₂ := eq7285 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq7285 eq29550
    | exact resolve eq29550 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7285 eq29550
  have eq29862 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29792 X0 X1 X2
       have i₂ := eq7631 X0
       grind)
    | exact superpose eq7631 eq29792
    | exact resolve eq29792 eq7631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7631 eq29792
  have eq31734 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq24651
  have eq31792 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31734
  have eq31848 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq31792
       grind)
    | exact superpose eq31792 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq31792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31853 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq879 x y
       have i₂ := eq31792
       grind)
    | exact superpose eq31792 eq879
    | (have j0 := eq879 x y
       grind)
    | exact resolve eq879 eq31792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq31792
  have eq31857 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31853
  have eq31858 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31848
  have eq31862 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31857
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31857
    | exact resolve eq31857 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31857
  have eq31867 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31858
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31858
    | exact resolve eq31858 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31858
  have eq31868 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31867
  have eq31880 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31862
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31862
    | exact resolve eq31862 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31862
  have eq31887 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq31880
    | exact resolve eq31880 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31880
  have eq31888 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq31887
  have eq31895 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31888
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31888
    | exact resolve eq31888 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31888
  have eq31902 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31895
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31895
    | exact resolve eq31895 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31895
  have eq31961 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq241 x x x
       have i₂ := eq31868
       grind)
    | exact superpose eq31868 eq241
    | exact resolve eq241 eq31868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq31868
  have eq32003 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31961 x
       have i₂ := eq9930 (M.op x y) x
       grind)
    | (have i₁ := eq31961 x
       have i₂ := eq9930 (M.op x y) x
       grind)
    | exact superpose eq9930 eq31961
    | (have j0 := eq31961 x
       grind)
    | exact resolve eq31961 eq9930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9930 eq31961
  have eq32025 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32003
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32003
    | exact resolve eq32003 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32003
  have eq32030 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3725 eq32025
    | exact resolve eq32025 eq3725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32025
  have eq42552 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3725 eq163
    | exact resolve eq163 eq3725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq42553 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq3725 eq42552
    | exact resolve eq42552 eq3725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725 eq42552
  have eq84320 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32030 eq42553
    | exact resolve eq42553 eq32030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32030 eq42553
  have eq84384 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq84320
  have eq84391 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq84384
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq84384
    | exact resolve eq84384 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84384
  have eq84399 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq84391 eq158
    | exact resolve eq158 eq84391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84391
  have eq84439 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq84399
    | exact resolve eq84399 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq84399
  have eq120861 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq31902 eq29862
    | exact resolve eq29862 eq31902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29862
  have eq121049 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq27 eq120861
    | (have j0 := eq120861 X0 X1
       grind)
    | exact resolve eq120861 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120861
  have eq360828 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27903 eq121049
    | exact resolve eq121049 eq27903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121049
  have eq360934 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq360828
  have eq361333 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27907 eq31902
    | exact resolve eq31902 eq27907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27907 eq31902
  have eq361677 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq361333
  have eq361779 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq361677 eq27903
    | exact resolve eq27903 eq361677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27903 eq361677
  have eq361916 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq361779
  have eq362017 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq361916 eq360934
    | exact resolve eq360934 eq361916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360934 eq361916
  have eq362127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq362017
  have eq362173 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq362127
       have r₂ := eq28
       grind)
    | exact resolve eq362127 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362127
  have eq477262 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq84439 eq9354
    | (have j0 := eq9354 (M.op x y)
       grind)
    | exact resolve eq9354 eq84439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9354
  have eq477338 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq477262
    | exact resolve eq477262 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477262
  have eq477383 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq477338
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq477338
    | exact resolve eq477338 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477338
  have eq477425 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq477383
       have r₂ := eq362173
       grind)
    | exact resolve eq477383 eq362173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362173 eq477383
  have eq477440 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq477425
    | exact resolve eq477425 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477425
  have eq477454 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq477440
    | exact resolve eq477440 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477440
  have eq477455 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq477454
  have eq477462 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq477455
  have eq477772 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq477462 eq158
    | exact resolve eq158 eq477462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq477462
  have eq477855 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq477772
    | exact resolve eq477772 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq477772
  have eq477884 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq477855 eq84439
    | exact resolve eq84439 eq477855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84439 eq477855
  have eq477930 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq477884
  have eq478018 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq477930 eq28
    | exact resolve eq28 eq477930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478021 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq477930 eq67
    | (have r₁ := eq67
       have r₂ := eq477930
       grind)
    | exact resolve eq67 eq477930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq478022 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq477930 eq217
    | exact resolve eq217 eq477930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq478074 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq477930 eq13271
    | exact resolve eq13271 eq477930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13271 eq477930
  have eq478687 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq478021
  have eq478778 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9822 eq478074
    | exact resolve eq478074 eq9822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9822 eq478074
  have eq478795 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq478022
    | exact resolve eq478022 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478022
  have eq478929 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq478778
  have eq479813 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq478929 eq61
    | exact resolve eq61 eq478929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq479874 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq479813
    | exact resolve eq479813 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479813
  have eq479933 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq479874
       grind)
    | exact superpose eq479874 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq479874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479946 : y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq479933
  have eq686481 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq478687 eq98
    | exact resolve eq98 eq478687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq478687
  have eq686552 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq686481
    | exact resolve eq686481 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq686481
  have eq686914 : (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq686552
  have eq690672 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq686914 eq101
    | exact resolve eq101 eq686914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq686914
  have eq690716 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by grind
  clear eq690672
  have eq690729 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq690716
       have r₂ := eq478018
       grind)
    | exact resolve eq690716 eq478018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690716
  have eq690734 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq690729
       have r₂ := eq66
       grind)
    | exact resolve eq690729 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq690729
  have eq690764 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq690734
       grind)
    | exact superpose eq690734 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq690734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690771 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8426 y x
       have i₂ := eq690734
       grind)
    | exact superpose eq690734 eq8426
    | (have j0 := eq8426 y x
       grind)
    | exact resolve eq8426 eq690734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8426 eq690734
  have eq690773 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq690771
  have eq690774 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq690764
  have eq690778 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq690773
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq690773
    | exact resolve eq690773 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690773
  have eq690785 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq690774
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq690774
    | exact resolve eq690774 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690774
  have eq690805 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq690778
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq690778
    | exact resolve eq690778 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690778
  have eq690812 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq690785
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq690785
    | exact resolve eq690785 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690785
  have eq690818 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq690805
    | exact resolve eq690805 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690805
  have eq690829 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq690818
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq690818
    | exact resolve eq690818 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690818
  have eq690984 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9457 x
       have i₂ := eq690812
       grind)
    | exact superpose eq690812 eq9457
    | exact resolve eq9457 eq690812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9457 eq690812
  have eq691407 : x = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq690984
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq690984
    | exact resolve eq690984 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690984
  have eq691408 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq691407
  have eq691552 : y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7658 x
       have i₂ := eq690829
       grind)
    | exact superpose eq690829 eq7658
    | exact resolve eq7658 eq690829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7658 eq690829
  have eq691986 : y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq691552
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq691552
    | exact resolve eq691552 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691552
  have eq693366 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq691408
       grind)
    | exact superpose eq691408 eq45
    | exact resolve eq45 eq691408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691408
  have eq693482 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq693366
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq693366
    | exact resolve eq693366 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693366
  have eq703052 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq691986 eq9378
    | (have j0 := eq9378 y
       grind)
    | exact resolve eq9378 eq691986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9378 eq691986
  have eq703070 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq703052
  have eq703086 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq703070
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq703070
    | exact resolve eq703070 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703070
  have eq703087 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq703086
  have eq703114 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq703087
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq703087
    | exact resolve eq703087 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703087
  have eq713191 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq693482 eq478929
    | exact resolve eq478929 eq693482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478929 eq693482
  have eq713216 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq713191
  have eq720985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq703114 eq478795
    | exact resolve eq478795 eq703114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478795 eq703114
  have eq721342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq720985
  have eq721484 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq721342
       have r₂ := eq28
       grind)
    | exact resolve eq721342 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721342
  have eq722232 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq721484 eq713216
    | exact resolve eq713216 eq721484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713216 eq721484
  have eq722237 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq722232
  have eq722717 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq722237
       have r₂ := eq478018
       grind)
    | exact resolve eq722237 eq478018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478018 eq722237
  have eq724189 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq722717
  have eq2863502 : y ≠ y ∨ x = (M.op y y) ∨ x = (k x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq479946
       grind)
    | exact superpose eq479946 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq479946
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq479946
       grind)
    | exact resolve eq12 eq479946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479946
  have eq2863741 : y ≠ y ∨ x = (M.op y y) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq2863502
  have eq2863742 : x = (k x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq2863741
  have eq2921558 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq479874
       have i₂ := eq2863742
       grind)
    | exact superpose eq2863742 eq479874
    | exact resolve eq479874 eq2863742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479874 eq2863742
  have eq2921692 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq2921558
  have eq2921793 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2921692
       have r₂ := eq724189
       grind)
    | exact resolve eq2921692 eq724189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724189 eq2921692
  have eq2922409 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq2921793
       grind)
    | exact superpose eq2921793 eq53
    | exact resolve eq53 eq2921793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921793
  have eq2922811 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2922409
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2922409
    | exact resolve eq2922409 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922409
  have eq2922812 : x = (M.op x y) := by grind
  clear eq2922811
  have eq2923028 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2922812 eq21
    | exact resolve eq21 eq2922812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2923078 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2922812 eq210
    | exact resolve eq210 eq2922812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq2923698 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2923078
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2923078
    | exact resolve eq2923078 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2923078
  have eq2923743 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2923028
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2923028
    | exact resolve eq2923028 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2923028
  have eq2923763 : x = (M.op y y) := by
    first
    | exact superpose eq2922812 eq2923698
    | exact resolve eq2923698 eq2922812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922812 eq2923698
  have eq2923777 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2923743 eq27
    | exact resolve eq27 eq2923743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2925420 : y = (k x y) := by grind
  clear eq2923763
  have eq2927209 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq2925420
       grind)
    | exact superpose eq2925420 eq45
    | exact resolve eq45 eq2925420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq2927274 : (σ y) ≠ (σ y) ∨ (σ y) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9116 y
       have i₂ := eq2925420
       grind)
    | exact superpose eq2925420 eq9116
    | (have j0 := eq9116 y
       grind)
    | exact resolve eq9116 eq2925420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9116 eq2925420
  have eq2927354 : (σ y) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2927274
  have eq2927431 : (σ y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2923743 eq2927354
    | exact resolve eq2927354 eq2923743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927354
  have eq2927460 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2923743 eq2927209
    | exact resolve eq2927209 eq2923743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927209
  have eq2927532 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2927431
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2927431
    | exact resolve eq2927431 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927431
  have eq2927561 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2927460
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2927460
    | exact resolve eq2927460 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927460
  have eq2927633 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2927532
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2927532
    | exact resolve eq2927532 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2927532
  have eq2927723 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2923743 eq2927633
    | exact resolve eq2927633 eq2923743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923743 eq2927633
  have eq2953505 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2927723 eq53
    | exact resolve eq53 eq2927723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2927723
  have eq2953904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2923777 eq2953505
    | exact resolve eq2953505 eq2923777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2953505
  have eq2954169 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2953904
       have r₂ := eq28
       grind)
    | exact resolve eq2953904 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2953904
  have eq2955687 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2954169 eq2923777
    | exact resolve eq2923777 eq2954169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923777
  have eq2955689 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2954169 eq2927561
    | exact resolve eq2927561 eq2954169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927561 eq2954169
  have eq2960447 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2955689 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2955689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955689
  have eq2960500 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2960447
  have eq2960526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2955687 eq2960500
    | exact resolve eq2960500 eq2955687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955687 eq2960500
  have eq2960586 : False := by grind
  exact eq2960586

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_x_pyx_Equation1590 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1590 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq18
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
  clear eq23
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op (M.op X2 (M.op X1 X0)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X3 (M.op X2 (M.op X1 X0)) (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 X1)
       have i₂ := eq64 (M.op (M.op X0 X1) (M.op X1 X2)) X1 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X2 (M.op X1 X0) (M.op (M.op X1 X0) X1)
       have i₂ := eq69 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq69 eq64
    | exact resolve eq64 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = (M.op (M.op X1 X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X1 X3) (M.op X3 X0)) X1 X2
       have i₂ := eq69 X1 X3 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X1 X3 X2 (M.op X2 (M.op X3 X0))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq359 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq368 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq368 (M.op X1 X0) (k X0 X1) X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq368 (k X0 X1) (M.op X1 X0) X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq368 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq368 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq399 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq359 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq359 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq359 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq526 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X2) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X3 X2 (M.op X0 X1) X1
       have i₂ := eq65 X1 X0 X2 (M.op X1 X3)
       grind)
    | exact superpose eq65 eq63
    | exact resolve eq63 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq65
  have eq629 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 X1 X3 (M.op (M.op X2 X3) X0) X2
       have i₂ := eq85 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq85 eq179
    | exact resolve eq179 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7507 : ∀ X0 X2 : G, (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq69 X0 x X2
       have i₂ := eq399 X2 X0 x
       grind)
    | exact superpose eq399 eq69
    | (have j1 := eq399 X2 X0 X2
       grind)
    | exact resolve eq69 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq11197 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq390 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq11253 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11197 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11197
  have eq11254 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11253 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11253
  have eq11418 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq11254 (σ X0)
       grind)
    | exact superpose eq11254 eq15
    | exact resolve eq15 eq11254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11420 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq11254 (τ X0)
       grind)
    | exact superpose eq11254 eq32
    | exact resolve eq32 eq11254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq11435 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11420 X0
       have i₂ := eq11254 X0
       grind)
    | exact superpose eq11254 eq11420
    | exact resolve eq11420 eq11254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11420
  have eq11437 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11418 X0
       have i₂ := eq11254 X0
       grind)
    | exact superpose eq11254 eq11418
    | exact resolve eq11418 eq11254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11254 eq11418
  have eq11568 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq11435 X0
       grind)
    | exact superpose eq11435 eq9
    | exact resolve eq9 eq11435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11571 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (M.op (τ X0) (τ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (τ X0) (τ X0)
       have i₂ := eq11435 X0
       grind)
    | exact superpose eq11435 eq64
    | exact resolve eq64 eq11435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11655 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq11437 X0
       grind)
    | exact superpose eq11437 eq9
    | exact resolve eq9 eq11437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11658 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (σ X0) (σ X0)
       have i₂ := eq11437 X0
       grind)
    | exact superpose eq11437 eq64
    | exact resolve eq64 eq11437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11660 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X1 (σ X0) (σ X0)
       have i₂ := eq11437 X0
       grind)
    | exact superpose eq11437 eq69
    | exact resolve eq69 eq11437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq11688 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) (M.op (σ X0) X2)) = (M.op (σ (M.op X0 X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq526 (σ X0) X1 (σ X0) X2
       have i₂ := eq11437 X0
       grind)
    | exact superpose eq11437 eq526
    | exact resolve eq526 eq11437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq11711 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7507 (σ X0) X1
       have i₂ := eq11437 X0
       grind)
    | exact superpose eq11437 eq7507
    | (have j0 := eq7507 (σ X0) X1
       grind)
    | exact resolve eq7507 eq11437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12033 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (τ (M.op X0 X0))) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11568 X0 (τ (M.op X0 X0))
       have i₂ := eq11435 (M.op X0 X0)
       grind)
    | exact superpose eq11435 eq11568
    | exact resolve eq11568 eq11435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11435 eq11568
  have eq12198 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12033 X0
       have i₂ := eq11571 X0 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact superpose eq11571 eq12033
    | exact resolve eq12033 eq11571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11571 eq12033
  have eq14255 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11655 X0 (σ (M.op X0 X0))
       have i₂ := eq11437 (M.op X0 X0)
       grind)
    | exact superpose eq11437 eq11655
    | exact resolve eq11655 eq11437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11655
  have eq14420 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq14255 X0
       have i₂ := eq11658 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact superpose eq11658 eq14255
    | exact resolve eq14255 eq11658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14255
  have eq16420 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X1) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12198 X0
       have i₂ := eq87 X0 X0 X0 X1
       grind)
    | (have i₁ := eq12198 X0
       have i₂ := eq87 X0 X0 X1 X0
       grind)
    | exact superpose eq87 eq12198
    | exact resolve eq12198 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12198
  have eq16915 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X1) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14420 X0
       have i₂ := eq87 X0 X0 X0 X1
       grind)
    | (have i₁ := eq14420 X0
       have i₂ := eq87 X0 X0 X1 X0
       grind)
    | exact superpose eq87 eq14420
    | exact resolve eq14420 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq14420
  have eq21711 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq11711 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq11711 X0 (σ X0)
       grind)
    | exact superpose eq11711 eq10
    | (have j1 := eq11711 X1 X0
       grind)
    | exact resolve eq10 eq11711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11711
  have eq23775 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq21711 (σ X0) X1
       grind)
    | exact superpose eq21711 eq15
    | (have j1 := eq21711 (σ X0) X1
       grind)
    | exact resolve eq15 eq21711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21711
  have eq23791 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23775 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23775
    | (have j0 := eq23775 X0 X1
       grind)
    | exact resolve eq23775 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23775
  have eq25199 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23791 X0 X1
       have i₂ := eq7507 X1 X0
       grind)
    | exact superpose eq7507 eq23791
    | (have j0 := eq23791 X0 X1
       have j1 := eq7507 X1 X0
       grind)
    | exact resolve eq23791 eq7507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7507 eq23791
  have eq25423 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq25199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25199
  have eq26547 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25423 x y
       grind)
    | exact superpose eq25423 eq16
    | (have j1 := eq25423 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq25423 x y
       grind)
    | exact resolve eq16 eq25423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26821 : x = (M.op y y) := by grind
  clear eq26547
  have eq26992 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq11658 y X0
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq11658
    | exact resolve eq11658 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11658
  have eq26993 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq11660 y X0
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq11660
    | exact resolve eq11660 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11660
  have eq27004 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq25423 X0 y
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq25423
    | (have j0 := eq25423 X0 y
       grind)
    | exact resolve eq25423 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25423
  have eq27005 : ∀ X0 : G, (M.op x (M.op y (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq9
    | exact resolve eq9 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27006 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq9
    | exact resolve eq9 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27009 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y x) X0) := by
    intro X0
    first
    | (have i₁ := eq64 X0 y y
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq64
    | exact resolve eq64 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq27059 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq16915 y y
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq16915
    | exact resolve eq16915 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16915
  have eq27069 : y = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq27005 y
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq27005
    | exact resolve eq27005 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27005
  have eq28099 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq27006 x
       have i₂ := eq27009 (M.op x x)
       grind)
    | exact superpose eq27009 eq27006
    | exact resolve eq27006 eq27009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27006 eq27009
  have eq28506 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq85 (M.op x x) y X0
       have i₂ := eq28099
       grind)
    | exact superpose eq28099 eq85
    | exact resolve eq85 eq28099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28099
  have eq28575 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq28506 X0
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq28506
    | exact resolve eq28506 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28506
  have eq30704 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq85 (σ (M.op x x)) (σ y) X0
       have i₂ := eq27059
       grind)
    | exact superpose eq27059 eq85
    | exact resolve eq85 eq27059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq30714 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ (M.op x x)) (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 (σ (M.op x x)) X0 (σ y)
       have i₂ := eq27059
       grind)
    | exact superpose eq27059 eq179
    | exact resolve eq179 eq27059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq30729 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 X1)) = (M.op (M.op (σ y) X0) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1 (σ y) (σ (M.op x x))
       have i₂ := eq27059
       grind)
    | exact superpose eq27059 eq629
    | exact resolve eq629 eq27059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq30754 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 X1)) = (M.op (σ (M.op y y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30729 X0 X1
       have i₂ := eq11688 y X0 X1
       grind)
    | exact superpose eq11688 eq30729
    | exact resolve eq30729 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11688 eq30729
  have eq30761 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq30704 X0
       have i₂ := eq11437 y
       grind)
    | exact superpose eq11437 eq30704
    | exact resolve eq30704 eq11437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11437 eq30704
  have eq30780 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 X1)) = (M.op (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30754 X0 X1
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq30754
    | exact resolve eq30754 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30754
  have eq30788 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq30761 X0
       have i₂ := eq26821
       grind)
    | exact superpose eq26821 eq30761
    | exact resolve eq30761 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26821 eq30761
  have eq30811 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ x) (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30714 X0 X1
       have i₂ := eq30780 (M.op X0 (σ y)) X1
       grind)
    | exact superpose eq30780 eq30714
    | exact resolve eq30714 eq30780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30714 eq30780
  have eq38998 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) = (M.op (τ (M.op (σ y) (σ x))) (τ (M.op (M.op (σ y) X0) (M.op X0 (M.op (σ y) (σ x)))))) := by
    intro X0
    first
    | (have i₁ := eq16420 (M.op (σ y) (σ x)) X0
       have i₂ := eq26992 X0
       grind)
    | exact superpose eq26992 eq16420
    | exact resolve eq16420 eq26992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16420 eq26992
  have eq39133 : (τ (M.op (σ y) (σ x))) = (M.op (τ (M.op (σ y) (σ x))) (τ (σ x))) := by
    first
    | (have i₁ := eq38998 x
       have i₂ := eq9 (σ x) (σ y) x
       grind)
    | exact superpose eq9 eq38998
    | exact resolve eq38998 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38998
  have eq39323 : (τ (M.op (σ y) (σ x))) = (M.op (τ (M.op (σ y) (σ x))) x) := by
    first
    | (have i₁ := eq39133
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq39133
    | exact resolve eq39133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39133
  have eq41027 : (σ y) = (M.op (σ x) (M.op (M.op (σ (M.op x x)) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq30788 (M.op (M.op (σ (M.op x x)) (σ y)) (σ x))
       have i₂ := eq26993 (σ (M.op x x))
       grind)
    | exact superpose eq26993 eq30788
    | exact resolve eq30788 eq26993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26993
  have eq41059 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq41027
       have i₂ := eq30811 (σ (M.op x x)) (σ x)
       grind)
    | exact superpose eq30811 eq41027
    | exact resolve eq41027 eq30811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30811 eq41027
  have eq41208 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq41059
       have i₂ := eq30788 (M.op (σ y) (σ x))
       grind)
    | exact superpose eq30788 eq41059
    | exact resolve eq41059 eq30788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41059
  have eq45663 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x x) y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq30788 (σ y)
       have i₂ := eq27004 (M.op x x)
       grind)
    | exact superpose eq27004 eq30788
    | (have j1 := eq27004 (M.op x x)
       grind)
    | exact resolve eq30788 eq27004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27004 eq30788
  have eq45793 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45663
       have i₂ := eq28575 y
       grind)
    | exact superpose eq28575 eq45663
    | exact resolve eq45663 eq28575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28575 eq45663
  have eq45808 : x = (M.op x x) := by
    first
    | (have r₁ := eq45793
       have r₂ := eq16
       grind)
    | exact resolve eq45793 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45793
  have eq45820 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq27059
       have i₂ := eq45808
       grind)
    | exact superpose eq45808 eq27059
    | exact resolve eq27059 eq45808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27059 eq45808
  have eq46556 : (τ (σ y)) = (M.op (τ (σ y)) x) := by
    first
    | (have i₁ := eq39323
       have i₂ := eq45820
       grind)
    | exact superpose eq45820 eq39323
    | exact resolve eq39323 eq45820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39323
  have eq46561 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41208
       have i₂ := eq45820
       grind)
    | exact superpose eq45820 eq41208
    | exact resolve eq41208 eq45820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41208 eq45820
  have eq46750 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46561
       grind)
    | exact superpose eq46561 eq16
    | exact resolve eq16 eq46561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46561
  have eq46798 : y = (M.op y x) := by
    first
    | (have i₁ := eq46556
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq46556
    | exact resolve eq46556 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46556
  have eq46915 : y = (M.op x y) := by
    first
    | (have i₁ := eq27069
       have i₂ := eq46798
       grind)
    | exact superpose eq46798 eq27069
    | exact resolve eq27069 eq46798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27069 eq46798
  have eq47347 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq46750
       have i₂ := eq46915
       grind)
    | exact superpose eq46915 eq46750
    | exact resolve eq46750 eq46915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46750 eq46915
  have eq47360 : False := by grind
  exact eq47360

/-- `Equation1630`: `x = (x ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation1630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq20 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq20 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq32 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq36 X1 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq36 X0 X1
       grind)
    | exact resolve eq40 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq40
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq21 X1
       grind)
    | exact superpose eq21 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq45
  have eq102 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq106 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq48 X0 X1
       grind)
    | (have r₁ := eq102 X0 X1
       have r₂ := eq48 X0 X1
       grind)
    | (have r₁ := eq102 X1 X1
       have r₂ := eq48 X1 X1
       grind)
    | exact resolve eq102 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq102
  have eq239 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq106 (σ X0) (σ X1)
       grind)
    | exact superpose eq106 eq15
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 X1
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq239
    | exact resolve eq239 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq239
  have eq246 : False := by grind
  exact eq246

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq61 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq64 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq59 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq59 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq60 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq60 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq60 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq75 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq61 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq61 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq70
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       have j1 := eq64 X1 X0
       grind)
    | (have r₁ := eq75 X0 X1
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq75 X1 X0
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq75 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq75
  have eq193 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq198 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       have j1 := eq88 X1 X0
       grind)
    | (have r₁ := eq193 X1 X0
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq193 X0 X0
       have r₂ := eq88 X0 X0
       grind)
    | exact resolve eq193 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq193
  have eq293 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq198 (σ X1) (σ X0)
       grind)
    | exact superpose eq198 eq15
    | exact resolve eq15 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq198 X1 X0
       grind)
    | exact superpose eq198 eq293
    | exact resolve eq293 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq293
  have eq300 : False := by grind
  exact eq300

/-- `Equation1682`: `x = (y ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1682 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1682 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1682.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  clear eq18
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
  have eq527 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
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
  have eq551 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  clear eq19
  have eq554 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq577 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq554
    | (have j0 := eq554 X0 X1
       grind)
    | exact resolve eq554 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq3513 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq577 x y
       grind)
    | exact superpose eq577 eq16
    | (have j1 := eq577 x y
       grind)
    | exact resolve eq16 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3523 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq577 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq3717 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq551
    | exact resolve eq551 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq3775 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3717 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3717
    | (have j0 := eq3717 X0 X1
       grind)
    | exact resolve eq3717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3717
  have eq7581 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3513
       have i₂ := eq3775 y x
       grind)
    | exact superpose eq3775 eq3513
    | (have j1 := eq3775 y x
       grind)
    | (have r₁ := eq3513
       have r₂ := eq3775 y x
       grind)
    | (have r₁ := eq3513
       have r₂ := eq3775 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3513
       have r₂ := eq3775 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3513 eq3775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3513 eq3775
  have eq7582 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7581
  have eq7594 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3523 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3523
    | (have j0 := eq3523 (τ X0) (τ X1)
       grind)
    | exact resolve eq3523 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq7661 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7594 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7594
    | (have j0 := eq7594 X0 X1
       grind)
    | exact resolve eq7594 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7594
  have eq7696 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7661 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7661
    | (have j0 := eq7661 X0 X1
       grind)
    | exact resolve eq7661 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7661
  have eq7728 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7696 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7696
    | (have j0 := eq7696 X0 X1
       grind)
    | exact resolve eq7696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7696
  have eq7754 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7728 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7728
    | (have j0 := eq7728 X0 X1
       grind)
    | exact resolve eq7728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7728
  have eq7773 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7754 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7754
    | (have j0 := eq7754 X0 X1
       grind)
    | exact resolve eq7754 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7754
  have eq7790 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7773 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7773
    | (have j0 := eq7773 X0 X1
       grind)
    | exact resolve eq7773 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7773
  have eq7803 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7790 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7790
    | (have j0 := eq7790 X0 X1
       grind)
    | exact resolve eq7790 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7790
  have eq15517 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7582
       grind)
    | exact superpose eq7582 eq16
    | exact resolve eq16 eq7582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7582
  have eq15518 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15517
       have r₂ := eq22 x
       grind)
    | exact resolve eq15517 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15517
  have eq15521 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq15518
       grind)
    | exact superpose eq15518 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15518
       grind)
    | exact resolve eq13 eq15518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15518
  have eq15523 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15521
  have eq17028 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15523
       grind)
    | exact superpose eq15523 eq16
    | exact resolve eq16 eq15523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15523
  have eq17029 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq17028
       have r₂ := eq22 x
       grind)
    | exact resolve eq17028 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17028
  have eq17032 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq527 x (σ y)
       have i₂ := eq17029
       grind)
    | exact superpose eq17029 eq527
    | (have j0 := eq527 x (σ y)
       grind)
    | (have r₁ := eq527 x (σ y)
       have r₂ := eq17029
       grind)
    | exact resolve eq527 eq17029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17029
  have eq17045 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq17032
  have eq17046 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq17045
  have eq17052 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17046
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17046
    | exact resolve eq17046 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17046
  have eq17064 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3523 x y
       have i₂ := eq17052
       grind)
    | exact superpose eq17052 eq3523
    | (have j0 := eq3523 x y
       grind)
    | (have r₁ := eq3523 x y
       have r₂ := eq17052
       grind)
    | exact resolve eq3523 eq17052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17052
  have eq17090 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq17064
  have eq17091 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq17090
  have eq17095 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq3523 x y
       grind)
    | (have r₁ := eq17091
       have r₂ := eq3523 x y
       grind)
    | exact resolve eq17091 eq3523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523 eq17091
  have eq17098 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17095
       grind)
    | exact superpose eq17095 eq16
    | exact resolve eq16 eq17095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17099 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq527 x (σ y)
       have i₂ := eq17095
       grind)
    | exact superpose eq17095 eq527
    | (have j0 := eq527 x (σ y)
       grind)
    | (have r₁ := eq527 x (σ y)
       have r₂ := eq17095
       grind)
    | exact resolve eq527 eq17095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq17095
  have eq17112 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq17099
  have eq17113 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq17112
  have eq17119 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17113
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17113
    | exact resolve eq17113 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17113
  have eq17129 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17119
       grind)
    | exact superpose eq17119 eq10
    | exact resolve eq10 eq17119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17119
  have eq17296 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17129
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17129
    | exact resolve eq17129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17129
  have eq17298 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17296
       grind)
    | exact superpose eq17296 eq16
    | exact resolve eq16 eq17296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17296
  have eq17299 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq17298
       have r₂ := eq22 x
       grind)
    | exact resolve eq17298 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17298
  have eq17312 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq17299
       grind)
    | exact superpose eq17299 eq10
    | exact resolve eq10 eq17299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17299
  have eq17480 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq17312
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq17312
    | exact resolve eq17312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17312
  have eq17509 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7803 x y
       have i₂ := eq17480
       grind)
    | exact superpose eq17480 eq7803
    | (have j0 := eq7803 x y
       grind)
    | (have r₁ := eq7803 x y
       have r₂ := eq17480
       grind)
    | exact resolve eq7803 eq17480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7803 eq17480
  have eq17512 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17509
  have eq17516 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17098
       have i₂ := eq17512
       grind)
    | exact superpose eq17512 eq17098
    | exact resolve eq17098 eq17512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17098 eq17512
  have eq17525 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq17516
  have eq17526 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17525
       grind)
    | exact superpose eq17525 eq16
    | exact resolve eq16 eq17525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17525
  have eq17529 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq17526
       have r₂ := eq22 x
       grind)
    | exact resolve eq17526 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17526
  have eq17530 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17529
       grind)
    | exact superpose eq17529 eq16
    | exact resolve eq16 eq17529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17531 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17529
       grind)
    | exact superpose eq17529 eq10
    | exact resolve eq10 eq17529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17529
  have eq17698 : x = y := by
    first
    | (have i₁ := eq17531
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17531
    | exact resolve eq17531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17531
  have eq17699 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17530
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq17530
    | exact resolve eq17530 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17530
  have eq17700 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17699
       have i₂ := eq17698
       grind)
    | exact superpose eq17698 eq17699
    | exact resolve eq17699 eq17698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17698 eq17699
  have eq17701 : False := by grind
  exact eq17701

/-- `Equation1682`: `x = (y ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation1682 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1682 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1682.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq36 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq43 : ∀ X0 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
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
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq101 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq254 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq268 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq254 X0 X1 X2
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq254
    | (have j0 := eq254 X0 X1 X2
       grind)
    | exact resolve eq254 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq254
  have eq3284 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (k (k (σ X1) X2) X3) = (M.op (σ X0) (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq268 X0 X1 X2
       grind)
    | exact superpose eq268 eq13
    | (have j0 := eq13 (k (k (σ X1) X2) X3) (M.op (σ X0) (k (σ X1) X2))
       have j1 := eq268 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq268 X0 X1 X2
       grind)
    | exact resolve eq13 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq230528 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3284 X2 X0 X1 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284
  have eq230529 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq230528 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230528
  have eq230537 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq230529 X0 X1 X2
       have i₂ := eq36 X0 X1 X2
       grind)
    | exact superpose eq36 eq230529
    | (have j0 := eq230529 X0 X1 X2
       grind)
    | exact resolve eq230529 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq230529
  have eq230538 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq230537 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230537
  have eq231093 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (k X1 (τ X2))
       have i₂ := eq230538 X1 X2 (τ X0)
       grind)
    | exact superpose eq230538 eq19
    | (have j1 := eq230538 X1 X2 (τ X0)
       grind)
    | exact resolve eq19 eq230538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230538
  have eq231421 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231093 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231093
    | (have j0 := eq231093 X0 X1 X2
       grind)
    | exact resolve eq231093 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231093
  have eq231570 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231421 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq231421
    | (have j0 := eq231421 X0 X1 X2
       grind)
    | exact resolve eq231421 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231421
  have eq231708 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231570 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231570
    | (have j0 := eq231570 X0 X1 X2
       grind)
    | exact resolve eq231570 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231570
  have eq231930 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) ∨ (k X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231708 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231708
    | exact resolve eq231708 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231708
  have eq233274 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq233275 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = X2 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231930 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq231930
    | (have j0 := eq231930 (M.op X0 X1) X2 (M.op X2 (M.op X0 X1))
       have j1 := eq14 (M.op X0 X1) X2
       grind)
    | exact resolve eq231930 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231930
  have eq590374 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq233275 (M.op (M.op (M.op X0 X0) X0) X0) X0 x
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq233275
    | (have j0 := eq233275 X1 X0 (k X0 X1)
       grind)
    | exact resolve eq233275 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233275
  have eq591428 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0
       have i₂ := eq590374 X0 X1
       grind)
    | exact superpose eq590374 eq43
    | (have j1 := eq590374 X0 X1
       grind)
    | exact resolve eq43 eq590374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq590374
  have eq591611 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq591428 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591428
  have eq592111 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ X0 = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233274 X0 X1
       have i₂ := eq591611 X0 X1
       grind)
    | exact superpose eq591611 eq233274
    | (have j1 := eq591611 X0 X1
       grind)
    | exact resolve eq233274 eq591611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233274 eq591611
  have eq601968 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq592111 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592111
  have eq601969 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq601968 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601968
  have eq601970 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq601969 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601969
  have eq602531 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq601970 X1 (τ X0)
       grind)
    | exact superpose eq601970 eq19
    | (have j1 := eq601970 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq601970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq602921 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq601970 (σ X1) (σ X0)
       grind)
    | exact superpose eq601970 eq15
    | (have j1 := eq601970 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq601970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601970
  have eq606031 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq602531 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq602531
    | exact resolve eq602531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602531
  have eq606758 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq606031 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq606031
    | (have j0 := eq606031 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq606031 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606031
  have eq612379 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq602921 x y
       grind)
    | exact superpose eq602921 eq16
    | (have j1 := eq602921 x y
       grind)
    | exact resolve eq16 eq602921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602921
  have eq612764 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq612379
       have i₂ := eq606758 x y
       grind)
    | exact superpose eq606758 eq612379
    | (have j1 := eq606758 (σ x) (σ y)
       grind)
    | (have r₁ := eq612379
       have r₂ := eq606758 x y
       grind)
    | (have r₁ := eq612379
       have r₂ := eq606758 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq612379
       have r₂ := eq606758 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq612379 eq606758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606758 eq612379
  have eq612767 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq612764
  have eq614667 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq612767
       grind)
    | exact superpose eq612767 eq16
    | exact resolve eq16 eq612767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612767
  have eq614668 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq614667
       have r₂ := eq22 x
       grind)
    | exact resolve eq614667 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614667
  have eq614669 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq614668
       grind)
    | exact superpose eq614668 eq16
    | exact resolve eq16 eq614668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614670 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq614668
       grind)
    | exact superpose eq614668 eq10
    | exact resolve eq10 eq614668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614668
  have eq615212 : x = y := by
    first
    | (have i₁ := eq614670
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq614670
    | exact resolve eq614670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614670
  have eq615213 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq614669
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq614669
    | exact resolve eq614669 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq614669
  have eq615220 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq615213
       have i₂ := eq615212
       grind)
    | exact superpose eq615212 eq615213
    | exact resolve eq615213 eq615212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615212 eq615213
  have eq615221 : False := by grind
  exact eq615221
