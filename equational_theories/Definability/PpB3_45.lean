import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  clear eq22
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
  have eq54 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq36
  have eq58 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq24 (σ X0) (σ X0)
       grind)
    | exact superpose eq24 eq54
    | exact resolve eq54 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq75 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq181 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq75 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq75 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq75 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq189 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq190 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq192 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq190
    | (have j0 := eq190 X0 X1
       grind)
    | exact resolve eq190 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq188 X1 X0
       grind)
    | (have r₁ := eq192 X1 X0
       have r₂ := eq188 X0 X1
       grind)
    | (have r₁ := eq192 (k X1 X0) X1
       have r₂ := eq188 X0 X1
       grind)
    | (have r₁ := eq192 X1 X1
       have r₂ := eq188 X1 X1
       grind)
    | exact resolve eq192 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq192
  have eq642 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq196
    | exact resolve eq196 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq196 y x
       grind)
    | exact superpose eq196 eq16
    | (have j1 := eq196 y x
       grind)
    | exact resolve eq16 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq678 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq642 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq642
    | (have j0 := eq642 X0 X1
       grind)
    | exact resolve eq642 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq642
  have eq1114 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq678 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq678
    | exact resolve eq678 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq1177 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1114 (τ X1) X0
       grind)
    | exact superpose eq1114 eq18
    | (have j1 := eq1114 (τ X1) X0
       grind)
    | exact resolve eq18 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1522 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1177 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1177
    | exact resolve eq1177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1594 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1522 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1522
    | (have j0 := eq1522 X0 X1
       grind)
    | exact resolve eq1522 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq2114 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq654
       have i₂ := eq1594 y x
       grind)
    | exact superpose eq1594 eq654
    | (have j1 := eq1594 (σ y) (σ x)
       grind)
    | (have r₁ := eq654
       have r₂ := eq1594 y x
       grind)
    | exact resolve eq654 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq2115 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2114
  have eq2122 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2115
  have eq2345 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq654
       have i₂ := eq2122
       grind)
    | exact superpose eq2122 eq654
    | exact resolve eq654 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq2122
  have eq2346 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2345
  have eq2347 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2346
  have eq2389 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | (have i₁ := eq58 x
       have i₂ := eq2347
       grind)
    | exact superpose eq2347 eq58
    | exact resolve eq58 eq2347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq2409 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24 (σ x) (σ x)
       have i₂ := eq2347
       grind)
    | exact superpose eq2347 eq24
    | exact resolve eq24 eq2347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2347
  have eq2434 : y = (k y x) := by
    first
    | (have i₁ := eq2389
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2389
    | exact resolve eq2389 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq2446 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1114 y x
       have i₂ := eq2434
       grind)
    | exact superpose eq2434 eq1114
    | (have j0 := eq1114 y x
       grind)
    | exact resolve eq1114 eq2434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114 eq2434
  have eq2724 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2409
       grind)
    | exact superpose eq2409 eq16
    | exact resolve eq16 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2863 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2724
       have i₂ := eq2446
       grind)
    | exact superpose eq2446 eq2724
    | exact resolve eq2724 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446
  have eq2889 : y = (M.op x x) := by grind
  clear eq2863
  have eq2978 : y = (M.op x y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq2889
       grind)
    | exact superpose eq2889 eq24
    | exact resolve eq24 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2889
  have eq3105 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2724
       have i₂ := eq2978
       grind)
    | exact superpose eq2978 eq2724
    | exact resolve eq2724 eq2978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724 eq2978
  have eq3131 : False := by grind
  exact eq3131

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
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
  have eq159 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
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
  have eq526 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq541 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq1026 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq1051 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq4042 : ∀ X0 : G, (σ (k (σ (τ (τ X0))) (τ X0))) = (k (σ (k (σ (τ (τ X0))) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq159 X0
       have i₂ := eq541 (τ X0) (τ (τ X0))
       grind)
    | exact superpose eq541 eq159
    | (have j1 := eq541 (τ X0) (τ (τ X0))
       grind)
    | exact resolve eq159 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq541
  have eq4098 : ∀ X0 : G, (σ (k (σ (τ (τ X0))) (τ X0))) = (k (σ (k (σ (τ (τ X0))) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq4042 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4042
  have eq4101 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = (k (k (σ (σ (τ (τ X0)))) X0) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4098 X0
       have i₂ := eq19 X0 (σ (τ (τ X0)))
       grind)
    | exact superpose eq19 eq4098
    | (have j0 := eq4098 X0
       grind)
    | exact resolve eq4098 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4098
  have eq4107 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4101 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq4101
    | (have j0 := eq4101 X0
       grind)
    | exact resolve eq4101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4101
  have eq4108 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4107 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4107
    | (have j0 := eq4107 X0
       grind)
    | exact resolve eq4107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4107
  have eq4685 : ∀ X0 X1 : G, (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) = (M.op X1 (M.op (M.op (τ (τ X0)) X1) (τ (τ X0)))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (τ (τ X0)) (τ (τ X0))
       have i₂ := eq4108 X0
       grind)
    | exact superpose eq4108 eq88
    | (have j1 := eq4108 X0
       grind)
    | exact resolve eq88 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq4726 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4685 X0 X1
       have i₂ := eq66 (τ (τ X0)) X1
       grind)
    | exact superpose eq66 eq4685
    | (have j0 := eq4685 X0 X1
       grind)
    | exact resolve eq4685 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4685
  have eq6268 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq4726 (σ X0) X1
       grind)
    | exact superpose eq4726 eq23
    | (have j1 := eq4726 (σ X0) X1
       grind)
    | exact resolve eq23 eq4726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4726
  have eq6316 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6268 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6268
    | (have j0 := eq6268 X0 X1
       grind)
    | exact resolve eq6268 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6268
  have eq6356 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6316 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6316
    | (have j0 := eq6316 X0 X1
       grind)
    | exact resolve eq6316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6316
  have eq6392 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6356 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6356
    | (have j0 := eq6356 X0 X1
       grind)
    | exact resolve eq6356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6356
  have eq6466 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq6392 (σ X0) X1
       grind)
    | exact superpose eq6392 eq23
    | (have j1 := eq6392 (σ X0) X1
       grind)
    | exact resolve eq23 eq6392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392
  have eq6514 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6466 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6466
    | (have j0 := eq6466 X0 X1
       grind)
    | exact resolve eq6466 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6466
  have eq6554 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6514 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6514
    | (have j0 := eq6514 X0 X1
       grind)
    | exact resolve eq6514 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514
  have eq6590 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6554 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6554
    | (have j0 := eq6554 X0 X1
       grind)
    | exact resolve eq6554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6554
  have eq6664 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq6590 (σ X0) X1
       grind)
    | exact superpose eq6590 eq23
    | (have j1 := eq6590 (σ X0) X1
       grind)
    | exact resolve eq23 eq6590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6590
  have eq6712 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6664 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6664
    | (have j0 := eq6664 X0 X1
       grind)
    | exact resolve eq6664 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6664
  have eq6752 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6712 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6712
    | (have j0 := eq6712 X0 X1
       grind)
    | exact resolve eq6712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6712
  have eq29197 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq1051
  have eq29214 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29197 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29197
  have eq29230 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq6752 eq29214
    | (have j0 := eq29214 X0
       have j1 := eq6752 X0 (σ X0)
       grind)
    | exact resolve eq29214 eq6752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6752 eq29214
  have eq29283 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29230 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq29230
    | (have j0 := eq29230 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq29230 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29307 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq29230 (τ X0)
       grind)
    | exact superpose eq29230 eq19
    | (have j1 := eq29230 (τ X0)
       grind)
    | exact resolve eq19 eq29230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29230
  have eq29382 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq29283 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29283
  have eq29389 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq29307 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29307
    | (have j0 := eq29307 X0
       grind)
    | exact resolve eq29307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29307
  have eq29416 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29389 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29389
    | (have j0 := eq29389 X0
       grind)
    | exact resolve eq29389 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29389
  have eq32531 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1025 x y
       grind)
    | exact superpose eq1025 eq16
    | (have j1 := eq1025 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1025 x y
       grind)
    | exact resolve eq16 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32641 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq32531
  have eq32882 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0) (σ X0)
       have i₂ := eq29382 X0
       grind)
    | exact superpose eq29382 eq68
    | (have j1 := eq29382 X0
       grind)
    | exact resolve eq68 eq29382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29382
  have eq91288 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq70 (σ y) (σ x) X0
       have i₂ := eq32641
       grind)
    | exact superpose eq32641 eq70
    | exact resolve eq70 eq32641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91479 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq91288 X0
       have i₂ := eq66 (σ y) X0
       grind)
    | exact superpose eq66 eq91288
    | exact resolve eq91288 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91288
  have eq92255 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq91479 eq32641
    | exact resolve eq32641 eq91479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32641
  have eq92258 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) x) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq36 x
       have i₂ := eq91479 X0
       grind)
    | exact superpose eq91479 eq36
    | (have j1 := eq91479 X0
       grind)
    | exact resolve eq36 eq91479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91479
  have eq92415 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq92258 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq92258
    | (have j0 := eq92258 X0
       grind)
    | exact resolve eq92258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92258
  have eq92429 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq92415 (σ y)
       grind)
    | exact superpose eq92415 eq36
    | exact resolve eq36 eq92415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92415
  have eq92604 : y = (k y y) ∨ y = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92429
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq92429
    | exact resolve eq92429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92429
  have eq92614 : y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq92604
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq92604 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92604
  have eq92687 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq92614
       grind)
    | exact superpose eq92614 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq92614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92614
  have eq92688 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq92687
  have eq92729 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq88 X0 y y
       have i₂ := eq92688
       grind)
    | exact superpose eq92688 eq88
    | exact resolve eq88 eq92688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92688
  have eq92868 : ∀ X0 : G, y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq92729 x
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq92729
    | exact resolve eq92729 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92729
  have eq92890 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq66 y x
       have i₂ := eq92868 X0
       grind)
    | exact superpose eq92868 eq66
    | (have j1 := eq92868 y
       grind)
    | exact resolve eq66 eq92868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92868
  have eq93453 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq92890 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92890
  have eq93454 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq93453
  have eq93524 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq88 X0 y y
       have i₂ := eq93454
       grind)
    | exact superpose eq93454 eq88
    | exact resolve eq88 eq93454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq93454
  have eq93663 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq93524 x
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq93524
    | exact resolve eq93524 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93524
  have eq93893 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq93663 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93663
  have eq93894 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq93893
  have eq93900 : y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq66 x y
       have i₂ := eq93894
       grind)
    | exact superpose eq93894 eq66
    | exact resolve eq66 eq93894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93984 : x ≠ y ∨ y = (M.op x x) ∨ (M.op y y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq526 x y
       have i₂ := eq93894
       grind)
    | exact superpose eq93894 eq526
    | exact resolve eq526 eq93894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq93894
  have eq94008 : x ≠ y ∨ y = (M.op x x) ∨ (M.op y y) = (k y x) := by grind
  clear eq93984
  have eq94025 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq66 x x
       have i₂ := eq93900
       grind)
    | exact superpose eq93900 eq66
    | exact resolve eq66 eq93900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93900
  have eq94132 : x = (M.op y x) := by grind
  clear eq94025
  have eq94150 : y = (M.op x y) := by
    first
    | (have i₁ := eq66 y x
       have i₂ := eq94132
       grind)
    | exact superpose eq94132 eq66
    | exact resolve eq66 eq94132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94258 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92255
       have i₂ := eq94132
       grind)
    | exact superpose eq94132 eq92255
    | exact resolve eq92255 eq94132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92255
  have eq94259 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94150
       grind)
    | exact superpose eq94150 eq16
    | exact resolve eq16 eq94150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94372 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94259
       have i₂ := eq1025 x y
       grind)
    | exact superpose eq1025 eq94259
    | (have j1 := eq1025 x y
       grind)
    | exact resolve eq94259 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq94373 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94372
       have i₂ := eq94150
       grind)
    | exact superpose eq94150 eq94372
    | exact resolve eq94372 eq94150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94150 eq94372
  have eq94374 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq94373
  have eq94375 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94374
       have i₂ := eq94132
       grind)
    | exact superpose eq94132 eq94374
    | exact resolve eq94374 eq94132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94374
  have eq96366 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68 (σ x) (σ x)
       have i₂ := eq94258
       grind)
    | exact superpose eq94258 eq68
    | exact resolve eq68 eq94258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq94258
  have eq96495 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq96366
       have r₂ := eq94259
       grind)
    | exact resolve eq96366 eq94259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96366
  have eq96709 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq96495 eq94375
    | exact resolve eq94375 eq96495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94375
  have eq96710 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq96495 eq96709
    | exact resolve eq96709 eq96495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96495 eq96709
  have eq96711 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq96710
  have eq96875 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq70 (σ x) (σ x) X0
       have i₂ := eq96711
       grind)
    | exact superpose eq96711 eq70
    | exact resolve eq70 eq96711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq96711
  have eq97023 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq96875 X0
       have i₂ := eq66 (σ x) X0
       grind)
    | exact superpose eq66 eq96875
    | exact resolve eq96875 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq96875
  have eq97223 : (σ y) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94259
       have i₂ := eq97023 (σ y)
       grind)
    | exact superpose eq97023 eq94259
    | (have r₁ := eq94259
       have r₂ := eq97023 (σ y)
       grind)
    | exact resolve eq94259 eq97023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97023
  have eq97349 : y = (M.op x x) ∨ x = y := by grind
  clear eq97223
  have eq97391 : y = (M.op x x) ∨ (M.op y y) = (k y x) := by
    first
    | (have r₁ := eq94008
       have r₂ := eq97349
       grind)
    | exact resolve eq94008 eq97349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94008
  have eq97405 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq32882 x
       have i₂ := eq97349
       grind)
    | exact superpose eq97349 eq32882
    | (have j0 := eq32882 x
       grind)
    | exact resolve eq32882 eq97349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32882
  have eq97520 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq97405
  have eq97564 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq97520
       have r₂ := eq94259
       grind)
    | exact resolve eq97520 eq94259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97520
  have eq97567 : y = (M.op x x) ∨ (M.op x x) = (k x x) := by
    first
    | exact superpose eq97349 eq97391
    | exact resolve eq97391 eq97349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97391
  have eq97569 : x = y ∨ (M.op x x) = (k x x) := by
    first
    | exact superpose eq29416 eq97567
    | (have j1 := eq29416 x
       grind)
    | exact resolve eq97567 eq29416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29416 eq97567
  have eq97570 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq97349 eq97569
    | exact resolve eq97569 eq97349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97349 eq97569
  have eq97830 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = y := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq97564
       grind)
    | exact superpose eq97564 eq36
    | exact resolve eq36 eq97564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq97564
  have eq97991 : x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq97830
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq97830
    | exact resolve eq97830 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97830
  have eq98007 : x = y ∨ x = y := by
    first
    | exact superpose eq97991 eq97570
    | exact resolve eq97570 eq97991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97570 eq97991
  have eq98096 : x = y := by grind
  clear eq98007
  have eq98103 : x = y := by grind
  clear eq98096
  have eq98109 : x = (M.op x x) := by
    first
    | (have i₁ := eq94132
       have i₂ := eq98103
       grind)
    | exact superpose eq98103 eq94132
    | exact resolve eq94132 eq98103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94132
  have eq98120 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq94259
       have i₂ := eq98103
       grind)
    | exact superpose eq98103 eq94259
    | exact resolve eq94259 eq98103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94259 eq98103
  have eq98132 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1026 x
       have i₂ := eq98109
       grind)
    | exact superpose eq98109 eq1026
    | exact resolve eq1026 eq98109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq98109
  have eq98244 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq98132
  have eq98287 : False := by grind
  exact eq98287

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_pyx_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) x) X0) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq66 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq82
    | exact resolve eq82 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq105 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq92 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq183 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq412 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq65
    | (have j0 := eq65 (σ y)
       grind)
    | exact resolve eq65 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq498 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X0)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq636 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq55
    | (have j1 := eq71 X0 X1
       grind)
    | exact resolve eq55 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq641 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq640 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq864 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (M.op (M.op (M.op X1 X2) X0) X1)
       have i₂ := eq105 X0 X1 X2
       grind)
    | exact superpose eq105 eq66
    | (have j1 := eq105 X0 X1 X2
       grind)
    | exact resolve eq66 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq105
  have eq920 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1446 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (M.op X0 X1))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq498 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq498
    | exact resolve eq498 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq4233 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq641 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq641
    | (have j0 := eq641 (τ X0)
       grind)
    | exact resolve eq641 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq641
  have eq4241 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4233 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4233
    | (have j0 := eq4233 X0
       grind)
    | exact resolve eq4233 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4233
  have eq4247 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4241 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4241
    | (have j0 := eq4241 X0
       grind)
    | exact resolve eq4241 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4241
  have eq4305 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1 X1
       have i₂ := eq104 X0 X1
       grind)
    | exact superpose eq104 eq61
    | (have j1 := eq104 X0 X1
       grind)
    | exact resolve eq61 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq104
  have eq4336 : x = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4305 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4305
    | (have j0 := eq4305 x y
       grind)
    | exact resolve eq4305 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4305
  have eq4365 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4336 eq46
    | exact resolve eq46 eq4336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4336
  have eq4379 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4365
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4365
    | exact resolve eq4365 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq8689 : (σ x) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq46 eq636
    | (have j0 := eq636 x (M.op x y)
       grind)
    | exact resolve eq636 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq8891 : (σ x) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq8689
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8689
    | exact resolve eq8689 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8689
  have eq8984 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq8891
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8891
    | exact resolve eq8891 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8891
  have eq9072 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq8984
    | exact resolve eq8984 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8984
  have eq9158 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq21 eq9072
    | exact resolve eq9072 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9072
  have eq9243 : (σ x) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq9158
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9158
    | exact resolve eq9158 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9158
  have eq9833 : (M.op x y) = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq51 eq864
    | exact resolve eq864 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq9836 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq52 eq864
    | exact resolve eq864 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq864
  have eq9866 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq9833 eq46
    | exact resolve eq46 eq9833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq9833
  have eq9886 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq21 eq9866
    | exact resolve eq9866 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9866
  have eq24179 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y))) (σ y)) := by
    first
    | exact superpose eq412 eq1446
    | exact resolve eq1446 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq1446
  have eq29300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq83 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq29300
    | exact resolve eq29300 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29300
  have eq29318 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq29307
       have r₂ := eq28
       grind)
    | exact resolve eq29307 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29307
  have eq29331 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29318 eq59
    | exact resolve eq59 eq29318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29318
  have eq29380 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq29331
  have eq29392 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29380 eq55
    | exact resolve eq55 eq29380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29380
  have eq29443 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq29392
    | exact resolve eq29392 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29392
  have eq29455 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59 y y
       have i₂ := eq29443
       grind)
    | exact superpose eq29443 eq59
    | exact resolve eq59 eq29443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29443
  have eq29504 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29455
  have eq29827 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55 y x
       have i₂ := eq29504
       grind)
    | exact superpose eq29504 eq55
    | exact resolve eq55 eq29504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29504
  have eq29878 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29827
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29827
    | exact resolve eq29827 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29827
  have eq29879 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29878 eq28
    | exact resolve eq28 eq29878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29915 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29878 eq9836
    | exact resolve eq9836 eq29878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9836 eq29878
  have eq32219 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq83 eq29915
    | exact resolve eq29915 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq29915
  have eq32253 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq32219
       have r₂ := eq29879
       grind)
    | exact resolve eq32219 eq29879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29879 eq32219
  have eq54487 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq59 y y
       have i₂ := eq32253
       grind)
    | exact superpose eq32253 eq59
    | exact resolve eq59 eq32253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32253
  have eq54570 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq54487
  have eq54603 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq55 y x
       have i₂ := eq54570
       grind)
    | exact superpose eq54570 eq55
    | exact resolve eq55 eq54570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54570
  have eq54690 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq54603
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54603
    | exact resolve eq54603 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54603
  have eq54691 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq54690
  have eq54694 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54691 eq29
    | exact resolve eq29 eq54691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq54699 : (k x x) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54691 eq50
    | exact resolve eq50 eq54691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq54808 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54691 eq4379
    | exact resolve eq4379 eq54691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4379 eq54691
  have eq54895 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq54808
  have eq54956 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq183 eq54699
    | exact resolve eq54699 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54699
  have eq54961 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq54694
    | exact resolve eq54694 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54694
  have eq55842 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54895 eq183
    | exact resolve eq183 eq54895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq54895
  have eq55889 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq55842
    | exact resolve eq55842 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq55842
  have eq61628 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54956 eq55889
    | exact resolve eq55889 eq54956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54956 eq55889
  have eq61645 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by grind
  clear eq61628
  have eq61695 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4247 x
       have i₂ := eq61645
       grind)
    | exact superpose eq61645 eq4247
    | (have j0 := eq4247 x
       grind)
    | exact resolve eq4247 eq61645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4247 eq61645
  have eq61716 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq61695
       have r₂ := eq54961
       grind)
    | exact resolve eq61695 eq54961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54961 eq61695
  have eq61747 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq920 x
       have i₂ := eq61716
       grind)
    | exact superpose eq61716 eq920
    | exact resolve eq920 eq61716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq61716
  have eq61896 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56 eq61747
    | exact resolve eq61747 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq61747
  have eq61910 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61896
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61896
    | exact resolve eq61896 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq61896
  have eq61911 : y = (M.op x y) := by grind
  clear eq61910
  have eq61915 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq61911 eq21
    | exact resolve eq21 eq61911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq62135 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq61915
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq61915
    | exact resolve eq61915 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq61915
  have eq62241 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq62135 eq27
    | exact resolve eq27 eq62135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq62343 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ (M.op x y)))) (σ (M.op x y))) := by
    first
    | exact superpose eq62135 eq24179
    | exact resolve eq24179 eq62135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24179
  have eq63196 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq9886 eq9243
    | exact resolve eq9243 eq9886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9243 eq9886
  have eq63300 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k x (M.op x y)) := by grind
  clear eq63196
  have eq63318 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (k x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq61911 eq63300
    | exact resolve eq63300 eq61911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61911 eq63300
  have eq142497 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (k x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq63318 eq55
    | exact resolve eq55 eq63318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63318
  have eq142631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq62241 eq142497
    | exact resolve eq142497 eq62241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142497
  have eq142634 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k x y) := by
    first
    | (have r₁ := eq142631
       have r₂ := eq28
       grind)
    | exact resolve eq142631 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142631
  have eq142656 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (k x y) := by
    first
    | exact superpose eq142634 eq55
    | exact resolve eq55 eq142634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142634
  have eq142801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq62241 eq142656
    | exact resolve eq142656 eq62241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142656
  have eq142809 : x = (k x y) := by
    first
    | (have r₁ := eq142801
       have r₂ := eq28
       grind)
    | exact resolve eq142801 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142801
  have eq142817 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq142809
       grind)
    | exact superpose eq142809 eq45
    | exact resolve eq45 eq142809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq142809
  have eq142858 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq62135 eq142817
    | exact resolve eq142817 eq62135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62135 eq142817
  have eq142873 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq142858
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq142858
    | exact resolve eq142858 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq142858
  have eq142946 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq142873 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq142873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142873
  have eq142959 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq62241 eq142946
    | exact resolve eq142946 eq62241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142946
  have eq143573 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq142959 eq55
    | exact resolve eq55 eq142959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142959
  have eq143706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq62241 eq143573
    | exact resolve eq143573 eq62241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143573
  have eq143709 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq143706
       have r₂ := eq28
       grind)
    | exact resolve eq143706 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143706
  have eq143731 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq143709 eq55
    | exact resolve eq55 eq143709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143709
  have eq143875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62241 eq143731
    | exact resolve eq143731 eq62241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143731
  have eq143884 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq143875
       have r₂ := eq28
       grind)
    | exact resolve eq143875 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143875
  have eq144007 : (σ (M.op x y)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (σ (M.op x y)))) (σ (M.op x y))) := by
    first
    | exact superpose eq143884 eq62343
    | exact resolve eq62343 eq143884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62343
  have eq144030 : (σ (M.op x y)) = (M.op (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq144007
       have i₂ := eq55 sF2 sF2
       grind)
    | exact superpose eq55 eq144007
    | exact resolve eq144007 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq144007
  have eq144107 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq144030
       have i₂ := eq59 sF2 sF1
       grind)
    | exact superpose eq59 eq144030
    | exact resolve eq144030 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq144030
  have eq144150 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq62241 eq144107
    | exact resolve eq144107 eq62241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144107
  have eq144164 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq143884 eq144150
    | exact resolve eq144150 eq143884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143884 eq144150
  have eq144168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62241 eq144164
    | exact resolve eq144164 eq62241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62241 eq144164
  have eq144170 : False := by grind
  exact eq144170

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
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
  clear eq19
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
  have eq77 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq23
    | exact resolve eq23 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq380 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq455 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq362 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq362
    | (have j0 := eq362 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq362 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 X2 : G, (k (τ X2) (k X1 X0)) = (τ (k X2 (M.op (σ X0) (σ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (k X1 X0)
       have i₂ := eq362 X1 X0
       grind)
    | exact superpose eq362 eq23
    | (have j1 := eq362 X1 X0
       grind)
    | exact resolve eq23 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq3953 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq380 (M.op (τ X1) X1) X1
       have i₂ := eq64 (τ X1) X1
       grind)
    | exact superpose eq64 eq380
    | (have j0 := eq380 (M.op (τ X0) X1) X0
       grind)
    | exact resolve eq380 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq4016 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3953 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3953
    | (have j0 := eq3953 X0 X1
       grind)
    | exact resolve eq3953 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953
  have eq9904 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq455 x y
       grind)
    | exact superpose eq455 eq16
    | (have j1 := eq455 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq455 x y
       grind)
    | exact resolve eq16 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq9974 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9904
  have eq54077 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77 x
       have i₂ := eq9974
       grind)
    | exact superpose eq9974 eq77
    | exact resolve eq77 eq9974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9974
  have eq54221 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq54077
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq54077
    | exact resolve eq54077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54077
  have eq54227 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq54221
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq54221
       have r₂ := eq13 y x
       grind)
    | exact resolve eq54221 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54221
  have eq54239 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ y = (k y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq68 (σ x) (σ y) X0
       have i₂ := eq54227
       grind)
    | exact superpose eq54227 eq68
    | exact resolve eq68 eq54227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54243 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op X0 (M.op (M.op (σ x) X0) (σ x))) ∨ y = (k y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq89 X0 (σ x) (σ y)
       have i₂ := eq54227
       grind)
    | exact superpose eq54227 eq89
    | exact resolve eq89 eq54227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq54424 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ y = (k y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq54243 x
       have i₂ := eq64 (σ x) x
       grind)
    | exact superpose eq64 eq54243
    | exact resolve eq54243 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54243
  have eq54428 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (k y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq54239 X0
       have i₂ := eq64 (σ x) X0
       grind)
    | exact superpose eq64 eq54239
    | exact resolve eq54239 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54239
  have eq54457 : (σ x) = (σ y) ∨ y = (k y x) ∨ y = (M.op x x) ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq54227
       have i₂ := eq54428 (σ y)
       grind)
    | exact superpose eq54428 eq54227
    | exact resolve eq54227 eq54428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54227
  have eq54460 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77 x
       have i₂ := eq54428 (σ x)
       grind)
    | exact superpose eq54428 eq77
    | exact resolve eq77 eq54428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq54428
  have eq54576 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq54457
  have eq54604 : y = (k y x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq54460
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq54460
    | exact resolve eq54460 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54460
  have eq54617 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq54576
       grind)
    | exact superpose eq54576 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq54576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54576
  have eq54618 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq54617
  have eq54622 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq54604
       grind)
    | exact superpose eq54604 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq54604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54604
  have eq54623 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x x) := by grind
  clear eq54622
  have eq56035 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq54618
       grind)
    | exact superpose eq54618 eq64
    | exact resolve eq64 eq54618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54618
  have eq56147 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq54623
       grind)
    | exact superpose eq54623 eq64
    | exact resolve eq64 eq54623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54623
  have eq56811 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq56035
       grind)
    | exact superpose eq56035 eq64
    | exact resolve eq64 eq56035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56035
  have eq56910 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq56811
  have eq57482 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq56147
       grind)
    | exact superpose eq56147 eq64
    | exact resolve eq64 eq56147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56147
  have eq57581 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq57482
  have eq57636 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq362 x x
       have i₂ := eq57581
       grind)
    | exact superpose eq57581 eq362
    | (have j0 := eq362 x x
       grind)
    | exact resolve eq362 eq57581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57637 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq57581
       grind)
    | exact superpose eq57581 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq57581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57581
  have eq57638 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq57637
  have eq57639 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq57636
  have eq57663 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 y x
       have i₂ := eq57638
       grind)
    | exact superpose eq57638 eq64
    | exact resolve eq64 eq57638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58005 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq68 (σ x) (σ x) X0
       have i₂ := eq57639
       grind)
    | exact superpose eq57639 eq68
    | exact resolve eq68 eq57639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57639
  have eq58144 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq58005 X0
       have i₂ := eq64 (σ x) X0
       grind)
    | exact superpose eq64 eq58005
    | exact resolve eq58005 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58005
  have eq58163 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58144 (σ y)
       grind)
    | exact superpose eq58144 eq16
    | exact resolve eq16 eq58144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58144
  have eq58309 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq56910 eq58163
    | exact resolve eq58163 eq56910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56910 eq58163
  have eq109975 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (τ X0) X1 X1
       have i₂ := eq4016 X0 X1
       grind)
    | exact superpose eq4016 eq68
    | (have j1 := eq4016 X0 X1
       grind)
    | exact resolve eq68 eq4016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110217 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | exact superpose eq109975 eq4016
    | (have j0 := eq4016 X0 X1
       have j1 := eq109975 X0 X1
       grind)
    | exact resolve eq4016 eq109975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016 eq109975
  have eq111997 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ (M.op (τ (σ X0)) X1))
       have i₂ := eq110217 (σ X0) X1
       grind)
    | exact superpose eq110217 eq29
    | (have j1 := eq110217 (σ X0) X1
       grind)
    | exact resolve eq29 eq110217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110217
  have eq112143 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq111997 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq111997
    | (have j0 := eq111997 X0 X1
       grind)
    | exact resolve eq111997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111997
  have eq112235 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq112143 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112143
    | (have j0 := eq112143 X0 X1
       grind)
    | exact resolve eq112143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112143
  have eq112294 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 (M.op X0 X1)) = X0 ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq112235 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112235
    | (have j0 := eq112235 X0 X1
       grind)
    | exact resolve eq112235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112235
  have eq112341 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq112294 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112294
    | (have j0 := eq112294 X0 X1
       grind)
    | exact resolve eq112294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112294
  have eq119582 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq112341 X0 (M.op X0 X1)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq112341
    | (have j0 := eq112341 X0 X1
       grind)
    | exact resolve eq112341 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112341
  have eq119882 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq119582 X0 X1
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq119582 X0 X1
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq119582 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq119582
  have eq120408 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 (M.op X0 X1)
       have i₂ := eq119882 X0 X1
       grind)
    | exact superpose eq119882 eq75
    | (have j1 := eq119882 X0 X1
       grind)
    | exact resolve eq75 eq119882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq119882
  have eq120559 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq120408 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120408
  have eq120726 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq120559 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq120559
    | exact resolve eq120559 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120788 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op (σ X0) X1)
       have i₂ := eq120559 (σ X0) X1
       grind)
    | exact superpose eq120559 eq29
    | exact resolve eq29 eq120559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq120898 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq120788 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120788
    | exact resolve eq120788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120788
  have eq121726 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ y = (k y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq120898 X0 (σ x)
       have i₂ := eq54424 (σ X0)
       grind)
    | exact superpose eq54424 eq120898
    | exact resolve eq120898 eq54424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54424
  have eq121963 : ∀ X0 : G, y = (k y x) ∨ (k X0 x) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq121726 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq121726
    | exact resolve eq121726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121726
  have eq136986 : y ≠ y ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq121963 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121963
  have eq136987 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq136986
  have eq136994 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq136987
       grind)
    | exact superpose eq136987 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq136987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136995 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq136994
  have eq136997 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq57663 eq136995
    | exact resolve eq136995 eq57663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57663 eq136995
  have eq137013 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq136997
       grind)
    | exact superpose eq136997 eq64
    | exact resolve eq64 eq136997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136997
  have eq137176 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq137013 eq58309
    | exact resolve eq58309 eq137013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58309 eq137013
  have eq137350 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq57638 eq137176
    | exact resolve eq137176 eq57638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57638 eq137176
  have eq137351 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq137350
  have eq137503 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120726 y x
       have i₂ := eq137351
       grind)
    | exact superpose eq137351 eq120726
    | exact resolve eq120726 eq137351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137351
  have eq154984 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq477 X0 X1 (σ X0)
       have i₂ := eq120559 (σ X0) (σ X1)
       grind)
    | exact superpose eq120559 eq477
    | (have j0 := eq477 X0 X1 x
       grind)
    | exact resolve eq477 eq120559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq155176 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 (k X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154984 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154984
    | (have j0 := eq154984 X0 X1
       grind)
    | exact resolve eq154984 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154984
  have eq256053 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq120898 X1 (σ X1)
       have i₂ := eq155176 X1 X0
       grind)
    | exact superpose eq155176 eq120898
    | (have j1 := eq155176 X1 X0
       grind)
    | exact resolve eq120898 eq155176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120898 eq155176
  have eq256452 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 ∨ (k X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq256053 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq256053
    | (have j0 := eq256053 X0 X1
       grind)
    | exact resolve eq256053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256053
  have eq256573 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x y) ∨ x = (k x (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256452 y x
       grind)
    | exact superpose eq256452 eq16
    | (have j1 := eq256452 y x
       grind)
    | exact resolve eq16 eq256452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256452
  have eq257275 : (σ x) ≠ (σ x) ∨ x = (k x y) ∨ x = (k x (k y x)) := by
    first
    | exact superpose eq137503 eq256573
    | exact resolve eq256573 eq137503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137503 eq256573
  have eq257276 : x = (k x (k y x)) ∨ x = (k x y) := by grind
  clear eq257275
  have eq257333 : x = (k x y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq257276
       have i₂ := eq136987
       grind)
    | exact superpose eq136987 eq257276
    | exact resolve eq257276 eq136987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136987 eq257276
  have eq257343 : y = (M.op x x) ∨ x = (k x y) := by grind
  clear eq257333
  have eq257563 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq120559 x x
       have i₂ := eq257343
       grind)
    | exact superpose eq257343 eq120559
    | exact resolve eq120559 eq257343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120559 eq257343
  have eq257715 : x = (k x y) := by grind
  clear eq257563
  have eq257912 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq257715
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq257715
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq257715 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257715
  have eq257952 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq68 y x X0
       have i₂ := eq257912
       grind)
    | exact superpose eq257912 eq68
    | exact resolve eq68 eq257912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258275 : x ≠ y ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  have eq258552 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq257952 X0
       have i₂ := eq64 y X0
       grind)
    | exact superpose eq64 eq257952
    | exact resolve eq257952 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257952
  have eq262977 : x = y ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq258552 eq257912
    | (have j1 := eq258552 x
       grind)
    | exact resolve eq257912 eq258552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257912 eq258552
  have eq263376 : x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq262977
       have r₂ := eq258275
       grind)
    | exact resolve eq262977 eq258275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258275 eq262977
  have eq263423 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq66 y y
       have i₂ := eq263376
       grind)
    | exact superpose eq263376 eq66
    | exact resolve eq66 eq263376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263376
  have eq263753 : x = (M.op y x) := by grind
  clear eq263423
  have eq263803 : y = (M.op x y) := by
    first
    | (have i₁ := eq64 y x
       have i₂ := eq263753
       grind)
    | exact superpose eq263753 eq64
    | exact resolve eq64 eq263753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263753
  have eq264132 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq263803
       grind)
    | exact superpose eq263803 eq16
    | exact resolve eq16 eq263803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264401 : y = (k y x) := by
    first
    | (have i₁ := eq120726 x y
       have i₂ := eq263803
       grind)
    | exact superpose eq263803 eq120726
    | exact resolve eq120726 eq263803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120726 eq263803
  have eq264573 : y = (k y x) := by grind
  clear eq264401
  have eq264591 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq362 y x
       have i₂ := eq264573
       grind)
    | exact superpose eq264573 eq362
    | (have j0 := eq362 y x
       grind)
    | exact resolve eq362 eq264573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq264573
  have eq264598 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq264591
       have r₂ := eq264132
       grind)
    | exact resolve eq264591 eq264132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264591
  have eq264606 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq264598
  have eq266066 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66 (σ x) (σ x)
       have i₂ := eq264606
       grind)
    | exact superpose eq264606 eq66
    | exact resolve eq66 eq264606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq264606
  have eq266387 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq266066
       have r₂ := eq264132
       grind)
    | exact resolve eq266066 eq264132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266066
  have eq266430 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq264132
       have i₂ := eq266387
       grind)
    | exact superpose eq266387 eq264132
    | exact resolve eq264132 eq266387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264132
  have eq266452 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 (σ x) (σ y) X0
       have i₂ := eq266387
       grind)
    | exact superpose eq266387 eq68
    | exact resolve eq68 eq266387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq267032 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq266452 X0
       have i₂ := eq64 (σ x) X0
       grind)
    | exact superpose eq64 eq266452
    | exact resolve eq266452 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq266452
  have eq270324 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq266387
       have i₂ := eq267032 (σ y)
       grind)
    | exact superpose eq267032 eq266387
    | exact resolve eq266387 eq267032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266387 eq267032
  have eq270790 : False := by grind
  exact eq270790

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq38 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
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
  have eq46 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq22 (τ X0) (τ X0)
       grind)
    | exact superpose eq22 eq38
    | exact resolve eq38 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq47 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq52 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq56 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq22 (σ X0) (σ X0)
       grind)
    | exact superpose eq22 eq52
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq61 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
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
  have eq72 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq85 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq47 (σ X0)
       grind)
    | exact superpose eq47 eq36
    | exact resolve eq36 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq95 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87
    | exact resolve eq87 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq16
    | (have j1 := eq74 x x
       grind)
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq58
    | (have j1 := eq74 X0 X0
       grind)
    | exact resolve eq58 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq171 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) (σ X0)
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq22
    | (have j1 := eq74 X1 X1
       grind)
    | exact resolve eq22 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq177 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq180 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq175 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq183 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq167 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq184 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq180
    | (have j0 := eq180 X0
       grind)
    | exact resolve eq180 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq186 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq183
    | (have j0 := eq183 X0
       grind)
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq208 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
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
  have eq490 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq178 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq178
    | (have j0 := eq178 (τ X0)
       grind)
    | exact resolve eq178 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq490 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq490
    | (have j0 := eq490 X0
       grind)
    | exact resolve eq490 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq495 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq492 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq492
    | (have j0 := eq492 X0
       grind)
    | exact resolve eq492 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq843 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq76 (τ X0) X0
       grind)
    | exact superpose eq76 eq47
    | (have j1 := eq76 (τ X0) X0
       grind)
    | exact resolve eq47 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq867 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq874 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq867 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq867
    | (have j0 := eq867 X0
       grind)
    | exact resolve eq867 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq956 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq874 X0
       grind)
    | exact superpose eq874 eq47
    | (have j1 := eq874 X0
       grind)
    | exact resolve eq47 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    grind
  clear eq874
  have eq987 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq960 X0
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq960
    | (have j0 := eq960 X0
       grind)
    | exact resolve eq960 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq990 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq956 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq956
    | (have j0 := eq956 X0
       grind)
    | exact resolve eq956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq998 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) (σ (τ X0))) = (σ (k (τ (k X0 X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq184 (τ X0)
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq184
    | (have j0 := eq184 (τ X0)
       grind)
    | exact resolve eq184 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1030 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) (σ (τ X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq998 X0
       have i₂ := eq19 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq19 eq998
    | (have j0 := eq998 X0
       grind)
    | exact resolve eq998 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1036 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1030 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1030
    | (have j0 := eq1030 X0
       grind)
    | exact resolve eq1030 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1041 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1036 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1036
    | (have j0 := eq1036 X0
       grind)
    | exact resolve eq1036 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1045 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1041 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1041
    | (have j0 := eq1041 X0
       grind)
    | exact resolve eq1041 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1390 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (τ X0) X1)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 (M.op (τ X0) X1)
       have i₂ := eq24 (τ X0) X1
       grind)
    | exact superpose eq24 eq72
    | (have j0 := eq72 X0 (τ X0)
       grind)
    | exact resolve eq72 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1765 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq166
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq166
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq166 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq1766 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1765
  have eq1896 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ (k X1 (τ X0))) X0) = X0 ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq171
    | exact resolve eq171 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1902 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ (k X1 X0)) (σ X0)) ∨ (σ X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 X1
       have i₂ := eq74 X1 X1
       grind)
    | exact superpose eq74 eq171
    | (have j0 := eq171 X1 X0
       have j1 := eq74 X0 X0
       grind)
    | exact resolve eq171 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq171
  have eq1933 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ (k X1 X0)) (σ X0)) ∨ (σ X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1902 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq1948 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ (k X1 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1933 X0 X1
       have j1 := eq178 X0
       grind)
    | (have r₁ := eq1933 X0 X1
       have r₂ := eq178 X0
       grind)
    | (have r₁ := eq1933 X0 X0
       have r₂ := eq178 X0
       grind)
    | (have r₁ := eq1933 X0 (k (k X0 X0) (k X0 X0))
       have r₂ := eq178 (k X0 X0)
       grind)
    | exact resolve eq1933 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1933
  have eq1949 : ∀ X0 X1 : G, (M.op (k (σ X1) X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1896 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1896
    | (have j0 := eq1896 X0 X1
       grind)
    | exact resolve eq1896 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1896
  have eq2696 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    grind
  clear eq186
  have eq2732 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2696 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2696
    | (have j0 := eq2696 X0
       grind)
    | exact resolve eq2696 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2696
  have eq3599 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq990 X0
       have i₂ := eq1045 X0
       grind)
    | exact superpose eq1045 eq990
    | (have j0 := eq990 X0
       have j1 := eq1045 X0
       grind)
    | exact resolve eq990 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990 eq1045
  have eq3641 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3599 X0
       have j1 := eq495 X0
       grind)
    | (have r₁ := eq3599 X0
       have r₂ := eq495 X0
       grind)
    | exact resolve eq3599 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq3599
  have eq3821 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (k X0 X0) X0
       have i₂ := eq3641 X0
       grind)
    | exact superpose eq3641 eq9
    | (have j1 := eq3641 X0
       grind)
    | exact resolve eq9 eq3641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3641
  have eq5770 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1949 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq1949
    | (have j0 := eq1949 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact resolve eq1949 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq1949
  have eq5822 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5770 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5770
  have eq5826 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5822 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5822
    | (have j0 := eq5822 (σ X0)
       grind)
    | exact resolve eq5822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5822
  have eq7093 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208 X0 X0 X0
       have i₂ := eq3821 X0 X1
       grind)
    | exact superpose eq3821 eq208
    | (have j1 := eq3821 X0 X2
       grind)
    | exact resolve eq208 eq3821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3821
  have eq7152 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7093 X0 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq7093
    | (have j0 := eq7093 X0 X1 X2
       grind)
    | exact resolve eq7093 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7093
  have eq10529 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7152 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7152
  have eq10530 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10529 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10529
  have eq10572 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq10530 X0
       grind)
    | exact superpose eq10530 eq9
    | exact resolve eq9 eq10530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10530
  have eq11264 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10572 (τ X0)
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq10572
    | exact resolve eq10572 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24969 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (τ (σ X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ X0) (σ X0)
       have i₂ := eq987 (σ X0)
       grind)
    | exact superpose eq987 eq61
    | (have j1 := eq987 (σ X0)
       grind)
    | exact resolve eq61 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq987
  have eq25028 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq24969 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24969
    | (have j0 := eq24969 X0
       grind)
    | exact resolve eq24969 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24969
  have eq25061 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (τ (σ X0)) X0) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25028 X0
       have i₂ := eq36 (σ X0) X0
       grind)
    | exact superpose eq36 eq25028
    | (have j0 := eq25028 X0
       grind)
    | exact resolve eq25028 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25028
  have eq25092 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq25061 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25061
    | (have j0 := eq25061 X0
       grind)
    | exact resolve eq25061 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25061
  have eq25919 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ X0) X1) (σ X0))) ∨ (σ X2) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ (k X2 X0)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208 X0 (σ X0) (σ X0)
       have i₂ := eq1948 X0 X1
       grind)
    | exact superpose eq1948 eq208
    | (have j1 := eq1948 X0 X2
       grind)
    | exact resolve eq208 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq25985 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X2 X0)) (σ X0)) ∨ (σ X2) = (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25919 X0 X1 X2
       have i₂ := eq22 (σ X0) X1
       grind)
    | exact superpose eq22 eq25919
    | (have j0 := eq25919 X0 X1 X2
       grind)
    | exact resolve eq25919 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25919
  have eq31162 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq95 x
       have i₂ := eq1766
       grind)
    | exact superpose eq1766 eq95
    | exact resolve eq95 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq1766
  have eq40852 : ∀ X0 : G, (τ X0) = (k (τ (k X0 X0)) (τ X0)) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2732 (τ X0)
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq2732
    | exact resolve eq2732 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732
  have eq40946 : ∀ X0 : G, (τ X0) = (τ (k (k X0 X0) X0)) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq40852 X0
       have i₂ := eq48 X0 (k X0 X0)
       grind)
    | exact superpose eq48 eq40852
    | (have j0 := eq40852 X0
       grind)
    | exact resolve eq40852 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40852
  have eq40981 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k X0 X0) ∨ (τ X0) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq40946 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq40946
    | (have j0 := eq40946 X0
       grind)
    | exact resolve eq40946 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40946
  have eq41005 : ∀ X0 : G, (τ X0) = (τ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40981 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40981
    | (have j0 := eq40981 X0
       grind)
    | exact resolve eq40981 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40981
  have eq76353 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ X0) X1) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 (σ X0) (σ X0)
       have i₂ := eq5826 X0
       grind)
    | exact superpose eq5826 eq208
    | (have j1 := eq5826 X0
       grind)
    | exact resolve eq208 eq5826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq76458 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5826
  have eq76488 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76353 X0 X1
       have i₂ := eq22 (σ X0) X1
       grind)
    | exact superpose eq22 eq76353
    | (have j0 := eq76353 X0 X1
       grind)
    | exact resolve eq76353 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76353
  have eq80980 : ∀ X0 X1 : G, (τ (σ (M.op (τ (σ X0)) X1))) = (k (τ (σ (M.op (τ (σ X0)) X1))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ (M.op (τ (σ X0)) X1)) X0
       have i₂ := eq1390 (σ X0) X1
       grind)
    | exact superpose eq1390 eq36
    | (have j1 := eq1390 (σ X0) X1
       grind)
    | exact resolve eq36 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq81010 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (k (M.op (τ (σ X0)) X1) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80980 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq80980
    | (have j0 := eq80980 X0 X1
       grind)
    | exact resolve eq80980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80980
  have eq81046 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81010 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81010
    | (have j0 := eq81010 X0 X1
       grind)
    | exact resolve eq81010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81010
  have eq81064 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81046 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81046
    | (have j0 := eq81046 X0 X1
       grind)
    | exact resolve eq81046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81046
  have eq81079 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq81064 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81064
    | (have j0 := eq81064 X0 X1
       grind)
    | exact resolve eq81064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81064
  have eq81087 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq81079 X0 X1
       have j1 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq81079 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq81079 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81079
  have eq83362 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq81087 X0 (k X0 X0)
       have i₂ := eq10572 X0
       grind)
    | exact superpose eq10572 eq81087
    | exact resolve eq81087 eq10572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10572
  have eq83439 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81087 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq81087
    | exact resolve eq81087 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81087
  have eq84743 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq25092 X0
       have i₂ := eq83362 X0
       grind)
    | exact superpose eq83362 eq25092
    | (have j0 := eq25092 X0
       have j1 := eq83362 X0
       grind)
    | exact resolve eq25092 eq83362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25092
  have eq84745 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq41005 X0
       have i₂ := eq83362 X0
       grind)
    | exact superpose eq83362 eq41005
    | (have j0 := eq41005 X0
       have j1 := eq83362 X0
       grind)
    | exact resolve eq41005 eq83362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41005 eq83362
  have eq84826 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq84745 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84745
  have eq84827 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq84743 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84743
  have eq85228 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq84827 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84827
  have eq86206 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11264 X0
       have i₂ := eq84826 X0
       grind)
    | exact superpose eq84826 eq11264
    | (have j1 := eq84826 X0
       grind)
    | exact resolve eq11264 eq84826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11264 eq84826
  have eq91607 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq86206
  have eq91824 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91607 X0
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq91607
    | (have j0 := eq91607 X0
       grind)
    | exact resolve eq91607 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq91607
  have eq109833 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) (σ X0)
       have i₂ := eq76488 X0 X1
       grind)
    | exact superpose eq76488 eq22
    | (have j1 := eq76488 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq22 eq76488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76488
  have eq114937 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq109833 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109833
  have eq114938 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq114937 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114937
  have eq115681 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq114938 X0
       grind)
    | exact superpose eq114938 eq22
    | exact resolve eq22 eq114938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115684 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ (M.op X0 X0)) (σ X0) X1
       have i₂ := eq114938 X0
       grind)
    | exact superpose eq114938 eq26
    | exact resolve eq26 eq114938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115839 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83439 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq114938 X0
       grind)
    | exact superpose eq114938 eq83439
    | exact resolve eq83439 eq114938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83439 eq114938
  have eq115843 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115839 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq115839
    | (have j0 := eq115839 X0
       grind)
    | exact resolve eq115839 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115839
  have eq115882 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq115843
  have eq115896 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115882 X0
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq115882
    | (have j0 := eq115882 X0
       grind)
    | exact resolve eq115882 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115882
  have eq115897 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq115896 X0
       have j1 := eq76458 X0
       grind)
    | (have r₁ := eq115896 X0
       have r₂ := eq76458 X0
       grind)
    | exact resolve eq115896 eq76458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76458 eq115896
  have eq116889 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq85228 (σ X0)
       have i₂ := eq115897 X0
       grind)
    | exact superpose eq115897 eq85228
    | (have j0 := eq85228 (σ X0)
       grind)
    | exact resolve eq85228 eq115897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85228
  have eq117073 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq116889 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq116889
    | (have j0 := eq116889 X0
       grind)
    | exact resolve eq116889 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116889
  have eq302414 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq43 X0 (σ X0)
       have i₂ := eq91824 (σ X0)
       grind)
    | exact superpose eq91824 eq43
    | (have j1 := eq91824 (σ X0)
       grind)
    | exact resolve eq43 eq91824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq91824
  have eq302548 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq302414 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq302414
    | (have j0 := eq302414 X0
       grind)
    | exact resolve eq302414 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302414
  have eq302684 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq302548 X0
       have i₂ := eq115897 X0
       grind)
    | exact superpose eq115897 eq302548
    | (have j0 := eq302548 X0
       grind)
    | exact resolve eq302548 eq115897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302548
  have eq302767 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq302684 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq302684
    | (have j0 := eq302684 X0
       grind)
    | exact resolve eq302684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302684
  have eq302850 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq302767 X0
       have i₂ := eq36 (σ X0) X0
       grind)
    | exact superpose eq36 eq302767
    | (have j0 := eq302767 X0
       grind)
    | exact resolve eq302767 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq302767
  have eq302928 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq302850 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq302850
    | (have j0 := eq302850 X0
       grind)
    | exact resolve eq302850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302850
  have eq302929 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq302928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302928
  have eq858832 : ∀ X0 X1 : G, (σ X1) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq25985 X1 (σ (k X0 X1)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25985
  have eq858833 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq858832 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858832
  have eq858835 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq858833 X0 X1
       have i₂ := eq302929 X1
       grind)
    | exact superpose eq302929 eq858833
    | (have j0 := eq858833 X0 X1
       grind)
    | exact resolve eq858833 eq302929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858833
  have eq1182729 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq858835 y x
       have i₂ := eq31162
       grind)
    | exact superpose eq31162 eq858835
    | (have j0 := eq858835 y x
       grind)
    | exact resolve eq858835 eq31162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31162 eq858835
  have eq1182732 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1182729
  have eq1182772 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1182732
       have i₂ := eq115897 x
       grind)
    | exact superpose eq115897 eq1182732
    | exact resolve eq1182732 eq115897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182732
  have eq1182795 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1182772
       have i₂ := eq115897 x
       grind)
    | exact superpose eq115897 eq1182772
    | exact resolve eq1182772 eq115897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115897 eq1182772
  have eq1182796 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1182795
  have eq1210011 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq117073 x
       have i₂ := eq1182796
       grind)
    | exact superpose eq1182796 eq117073
    | (have j0 := eq117073 x
       grind)
    | (have r₁ := eq117073 x
       have r₂ := eq1182796
       grind)
    | exact resolve eq117073 eq1182796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182796
  have eq1210343 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1210011
  have eq1210474 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have j1 := eq117073 x
       grind)
    | (have r₁ := eq1210343
       have r₂ := eq117073 x
       grind)
    | exact resolve eq1210343 eq117073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117073 eq1210343
  have eq1210563 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1210474
       have i₂ := eq302929 x
       grind)
    | exact superpose eq302929 eq1210474
    | exact resolve eq1210474 eq302929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302929 eq1210474
  have eq1210631 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq115681 x
       have i₂ := eq1210563
       grind)
    | exact superpose eq1210563 eq115681
    | exact resolve eq115681 eq1210563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115681
  have eq1210665 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1210563
       grind)
    | exact superpose eq1210563 eq10
    | exact resolve eq10 eq1210563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210563
  have eq1211304 : y = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1210665
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1210665
    | exact resolve eq1210665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210665
  have eq1214794 : y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq1211304
       grind)
    | exact superpose eq1211304 eq24
    | exact resolve eq24 eq1211304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1211304
  have eq1224588 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1210631
       grind)
    | exact superpose eq1210631 eq16
    | exact resolve eq16 eq1210631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210631
  have eq1228455 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1224588
       have i₂ := eq1214794
       grind)
    | exact superpose eq1214794 eq1224588
    | exact resolve eq1224588 eq1214794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214794 eq1224588
  have eq1228458 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq1228455
  have eq1228459 : (σ x) = (σ (M.op x x)) := by grind
  clear eq1228458
  have eq1228503 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq115684 x X0
       have i₂ := eq1228459
       grind)
    | exact superpose eq1228459 eq115684
    | exact resolve eq115684 eq1228459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115684
  have eq1228528 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1228459
       grind)
    | exact superpose eq1228459 eq10
    | exact resolve eq10 eq1228459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228459
  have eq1229173 : x = (M.op x x) := by
    first
    | (have i₁ := eq1228528
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1228528
    | exact resolve eq1228528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228528
  have eq1229192 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1228503 X0
       have i₂ := eq22 (σ x) X0
       grind)
    | exact superpose eq22 eq1228503
    | exact resolve eq1228503 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228503
  have eq1229724 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 x x X0
       have i₂ := eq1229173
       grind)
    | exact superpose eq1229173 eq26
    | exact resolve eq26 eq1229173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1229173
  have eq1230071 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1229724 X0
       have i₂ := eq22 x X0
       grind)
    | exact superpose eq22 eq1229724
    | exact resolve eq1229724 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1229724
  have eq1231907 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1229192 (σ y)
       grind)
    | exact superpose eq1229192 eq16
    | exact resolve eq16 eq1229192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229192
  have eq1232475 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1231907
       have i₂ := eq1230071 y
       grind)
    | exact superpose eq1230071 eq1231907
    | exact resolve eq1231907 eq1230071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230071 eq1231907
  have eq1232476 : False := by grind
  exact eq1232476

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_x_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq159 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
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
  have eq356 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 : G, (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) = (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
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
  have eq552 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq356 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq356
    | (have j0 := eq356 X0 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq356 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq578 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq356 X1 X0
       grind)
    | exact superpose eq356 eq15
    | (have j1 := eq356 X0 X0
       grind)
    | exact resolve eq15 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq1483 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 x
       have i₂ := eq374 (τ x) x
       grind)
    | exact superpose eq374 eq25
    | (have j1 := eq374 (τ X0) X0
       grind)
    | exact resolve eq25 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq1490 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1483 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq1492 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1490 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1490
    | (have j0 := eq1490 X0
       grind)
    | exact resolve eq1490 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1525 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq1492 (τ X0)
       grind)
    | exact superpose eq1492 eq19
    | (have j1 := eq1492 (τ X0)
       grind)
    | exact resolve eq19 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1531 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1525 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1525
    | (have j0 := eq1525 X0
       grind)
    | exact resolve eq1525 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1525
  have eq1547 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1531 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1531
    | (have j0 := eq1531 X0
       grind)
    | exact resolve eq1531 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531
  have eq4666 : ∀ X0 X1 : G, (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) = (M.op X1 (M.op (M.op (τ (τ X0)) X1) (τ (τ X0)))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (τ (τ X0)) (τ (τ X0))
       have i₂ := eq1547 X0
       grind)
    | exact superpose eq1547 eq88
    | (have j1 := eq1547 X0
       grind)
    | exact resolve eq88 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq4711 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4666 X0 X1
       have i₂ := eq66 (τ (τ X0)) X1
       grind)
    | exact superpose eq66 eq4666
    | (have j0 := eq4666 X0 X1
       grind)
    | exact resolve eq4666 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666
  have eq6511 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq4711 (σ X0) X1
       grind)
    | exact superpose eq4711 eq23
    | (have j1 := eq4711 (σ X0) X1
       grind)
    | exact resolve eq23 eq4711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4711
  have eq6559 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6511 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6511
    | (have j0 := eq6511 X0 X1
       grind)
    | exact resolve eq6511 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6511
  have eq6602 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6559 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6559
    | (have j0 := eq6559 X0 X1
       grind)
    | exact resolve eq6559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6559
  have eq6638 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6602 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6602
    | (have j0 := eq6602 X0 X1
       grind)
    | exact resolve eq6602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6602
  have eq6712 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq6638 (σ X0) X1
       grind)
    | exact superpose eq6638 eq23
    | (have j1 := eq6638 (σ X0) X1
       grind)
    | exact resolve eq23 eq6638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6638
  have eq6760 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6712 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6712
    | (have j0 := eq6712 X0 X1
       grind)
    | exact resolve eq6712 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6712
  have eq6803 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6760 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6760
    | (have j0 := eq6760 X0 X1
       grind)
    | exact resolve eq6760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6760
  have eq6839 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6803 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6803
    | (have j0 := eq6803 X0 X1
       grind)
    | exact resolve eq6803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6803
  have eq6913 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq6839 (σ X0) X1
       grind)
    | exact superpose eq6839 eq23
    | (have j1 := eq6839 (σ X0) X1
       grind)
    | exact resolve eq23 eq6839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6839
  have eq6961 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6913 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq6913
    | (have j0 := eq6913 X0 X1
       grind)
    | exact resolve eq6913 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6913
  have eq7003 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6961 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6961
    | (have j0 := eq6961 X0 X1
       grind)
    | exact resolve eq6961 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6961
  have eq8498 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq578
  have eq8514 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq8498 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8498
  have eq8530 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq7003 eq8514
    | (have j0 := eq8514 X0
       have j1 := eq7003 X0 (σ X0)
       grind)
    | exact resolve eq8514 eq7003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7003 eq8514
  have eq8555 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8530 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq8530
    | (have j0 := eq8530 X0
       have j1 := eq14 (σ (M.op X0 X0)) (σ X0)
       grind)
    | exact resolve eq8530 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8565 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq8530 (τ X0)
       grind)
    | exact superpose eq8530 eq19
    | (have j1 := eq8530 (τ X0)
       grind)
    | exact resolve eq19 eq8530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq8570 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq8530 X0
       grind)
    | exact superpose eq8530 eq10
    | (have j1 := eq8530 X0
       grind)
    | exact resolve eq10 eq8530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8530
  have eq8634 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8555 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8555
  have eq8639 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8565 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8565
    | (have j0 := eq8565 X0
       grind)
    | exact resolve eq8565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8565
  have eq8652 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8639 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8639
    | (have j0 := eq8639 X0
       grind)
    | exact resolve eq8639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8639
  have eq8663 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq8652 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq8652
    | (have j0 := eq8652 (τ X0)
       grind)
    | exact resolve eq8652 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8652
  have eq9011 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq8663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9038 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9011 (σ X0)
       have i₂ := eq30 X0 (σ X0)
       grind)
    | exact superpose eq30 eq9011
    | (have j0 := eq9011 (σ X0)
       grind)
    | exact resolve eq9011 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9011
  have eq9056 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9038 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9038
    | (have j0 := eq9038 X0
       grind)
    | exact resolve eq9038 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9038
  have eq9071 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9056 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9056
    | (have j0 := eq9056 X0
       grind)
    | exact resolve eq9056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9056
  have eq9355 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq552 x y
       grind)
    | exact superpose eq552 eq16
    | (have j1 := eq552 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq552 x y
       grind)
    | exact resolve eq16 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq9421 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq9355
  have eq23419 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq8634 eq553
    | (have j0 := eq553 X0
       have j1 := eq8634 X0
       grind)
    | exact resolve eq553 eq8634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq8634
  have eq23551 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq23419 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23419
  have eq23588 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq23551 eq8570
    | (have j0 := eq8570 X0
       have j1 := eq23551 X0
       grind)
    | exact resolve eq8570 eq23551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8570 eq23551
  have eq23738 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23588 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq23588
    | (have j0 := eq23588 X0
       grind)
    | exact resolve eq23588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23588
  have eq23910 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq23738 X0
       grind)
    | exact superpose eq23738 eq36
    | (have j1 := eq23738 X0
       grind)
    | exact resolve eq36 eq23738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq23911 : ∀ X0 : G, (τ (τ (σ (σ X0)))) = (k (τ (τ (σ (σ X0)))) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq399 X0
       have i₂ := eq23738 (σ X0)
       grind)
    | exact superpose eq23738 eq399
    | (have j1 := eq23738 (σ X0)
       grind)
    | exact resolve eq399 eq23738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq23921 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) (σ X0) X1
       have i₂ := eq23738 X0
       grind)
    | exact superpose eq23738 eq70
    | (have j1 := eq23738 X0
       grind)
    | exact resolve eq70 eq23738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23925 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ X0) X1) (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (σ X0) (σ X0)
       have i₂ := eq23738 X0
       grind)
    | exact superpose eq23738 eq88
    | (have j1 := eq23738 X0
       grind)
    | exact resolve eq88 eq23738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23738
  have eq24038 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23925 X0 X1
       have i₂ := eq66 (σ X0) X1
       grind)
    | exact superpose eq66 eq23925
    | (have j0 := eq23925 X0 X1
       grind)
    | exact resolve eq23925 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23925
  have eq24040 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23921 X0 X1
       have i₂ := eq66 (σ X0) X1
       grind)
    | exact superpose eq66 eq23921
    | (have j0 := eq23921 X0 X1
       grind)
    | exact resolve eq23921 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23921
  have eq24045 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq23911 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq23911
    | (have j0 := eq23911 X0
       grind)
    | exact resolve eq23911 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23911
  have eq24046 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23910 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23910
    | (have j0 := eq23910 X0
       grind)
    | exact resolve eq23910 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23910
  have eq24052 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24045 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24045
    | (have j0 := eq24045 X0
       grind)
    | exact resolve eq24045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24045
  have eq24055 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24052 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq24052
    | (have j0 := eq24052 X0
       grind)
    | exact resolve eq24052 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24052
  have eq24062 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24046 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq24046
    | exact resolve eq24046 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24170 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq24046 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24460 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq24040 (τ X0) X1
       grind)
    | exact superpose eq24040 eq33
    | (have j1 := eq24040 (τ X0) X1
       grind)
    | exact resolve eq33 eq24040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24040
  have eq24496 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24460 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24460
    | (have j0 := eq24460 X0 X1
       grind)
    | exact resolve eq24460 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24460
  have eq24601 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24038 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24038
    | (have j0 := eq24038 (τ X0) X1
       grind)
    | exact resolve eq24038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24913 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24601 X0 X1
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq24601
    | (have j0 := eq24601 X0 X1
       grind)
    | exact resolve eq24601 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24601
  have eq25163 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq24046 eq24055
    | (have j0 := eq24055 X0
       have j1 := eq24046 X0
       grind)
    | exact resolve eq24055 eq24046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24055
  have eq25351 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0) (σ X0)
       have i₂ := eq25163 X0
       grind)
    | exact superpose eq25163 eq66
    | (have j1 := eq25163 X0
       grind)
    | exact resolve eq66 eq25163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25523 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 (τ X0) (τ X0)
       have i₂ := eq24496 X0 X1
       grind)
    | exact superpose eq24496 eq66
    | (have j1 := eq24496 (τ (k X0 X0)) (τ X0)
       grind)
    | exact resolve eq66 eq24496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24496
  have eq25817 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq25351 (τ X0)
       have i₂ := eq365 X0 (τ X0)
       grind)
    | exact superpose eq365 eq25351
    | (have j0 := eq25351 (τ X0)
       have j1 := eq365 X0 (τ X0)
       grind)
    | exact resolve eq25351 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq25351
  have eq25927 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq25817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25817
  have eq25941 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq25927 X0
       have j1 := eq24170 (τ X0)
       grind)
    | (have r₁ := eq25927 X0
       have r₂ := eq24170 (τ X0)
       grind)
    | exact resolve eq25927 eq24170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24170 eq25927
  have eq25957 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq25941 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25941
    | (have j0 := eq25941 X0
       grind)
    | exact resolve eq25941 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25941
  have eq25968 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25957 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq25957
    | (have j0 := eq25957 X0
       grind)
    | exact resolve eq25957 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25957
  have eq26034 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 (k X0 X0)
       have i₂ := eq25968 X0
       grind)
    | exact superpose eq25968 eq25
    | (have j1 := eq25968 X0
       grind)
    | exact resolve eq25 eq25968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq25968
  have eq26088 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq24913 eq26034
    | (have j0 := eq26034 X0
       have j1 := eq24913 X0 (k X0 X0)
       grind)
    | exact resolve eq26034 eq24913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26034
  have eq26138 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26088 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq26088
    | (have j0 := eq26088 X0
       grind)
    | exact resolve eq26088 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26088
  have eq28999 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq24062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24062
  have eq29022 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25163 X0
       have j1 := eq9071 X0
       grind)
    | (have r₁ := eq25163 X0
       have r₂ := eq9071 X0
       grind)
    | exact resolve eq25163 eq9071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9071 eq25163
  have eq29113 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29022 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29022
    | (have j0 := eq29022 (τ X0)
       grind)
    | exact resolve eq29022 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29022
  have eq29265 : ∀ X0 : G, (M.op X0 X0) = (σ (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq8663 eq29113
    | (have j0 := eq29113 X0
       have j1 := eq8663 X0
       grind)
    | exact resolve eq29113 eq8663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8663 eq29113
  have eq29277 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq29265 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq29265
    | (have j0 := eq29265 X0
       grind)
    | exact resolve eq29265 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29265
  have eq29312 : ∀ X0 : G, (σ (σ (τ (τ X0)))) = (k (σ (σ (τ (τ X0)))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq159 X0
       have i₂ := eq29277 (τ X0)
       grind)
    | exact superpose eq29277 eq159
    | (have j1 := eq29277 (τ X0)
       grind)
    | exact resolve eq159 eq29277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq29326 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ X0)) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq70 (τ X0) (τ X0) X1
       have i₂ := eq29277 X0
       grind)
    | exact superpose eq29277 eq70
    | (have j1 := eq29277 X0
       grind)
    | exact resolve eq70 eq29277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29330 : ∀ X0 X1 : G, (M.op (M.op (τ X0) X1) (τ X0)) = (M.op X1 (M.op (M.op (τ X0) X1) (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (τ X0) (τ X0)
       have i₂ := eq29277 X0
       grind)
    | exact superpose eq29277 eq88
    | (have j1 := eq29277 X0
       grind)
    | exact resolve eq88 eq29277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq29277
  have eq29443 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29330 X0 X1
       have i₂ := eq66 (τ X0) X1
       grind)
    | exact superpose eq66 eq29330
    | (have j0 := eq29330 X0 X1
       grind)
    | exact resolve eq29330 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29330
  have eq29445 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29326 X0 X1
       have i₂ := eq66 (τ X0) X1
       grind)
    | exact superpose eq66 eq29326
    | (have j0 := eq29326 X0 X1
       grind)
    | exact resolve eq29326 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29326
  have eq29455 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29312 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq29312
    | (have j0 := eq29312 X0
       grind)
    | exact resolve eq29312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29312
  have eq29463 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29455 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29455
    | (have j0 := eq29455 X0
       grind)
    | exact resolve eq29455 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29455
  have eq29466 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29463 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq29463
    | (have j0 := eq29463 X0
       grind)
    | exact resolve eq29463 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29463
  have eq29468 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq24046 eq29466
    | (have j0 := eq29466 X0
       have j1 := eq24046 X0
       grind)
    | exact resolve eq29466 eq24046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24046 eq29466
  have eq30329 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29468 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29468
    | (have j0 := eq29468 (σ X0)
       grind)
    | exact resolve eq29468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29468
  have eq30484 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30329 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq30329
    | (have j0 := eq30329 X0
       grind)
    | exact resolve eq30329 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30329
  have eq47876 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) (k X0 X0)
       have i₂ := eq26138 X0
       grind)
    | exact superpose eq26138 eq14
    | (have j0 := eq14 (k X0 X0) (k X0 X0)
       have j1 := eq26138 X0
       grind)
    | exact resolve eq14 eq26138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26138
  have eq47877 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq47876 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47876
  have eq50814 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X1) (k X0 X0)) X1) = X1 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (k X0 X0) (k X0 X0) X1
       have i₂ := eq47877 X0
       grind)
    | exact superpose eq47877 eq70
    | (have j1 := eq47877 X0
       grind)
    | exact resolve eq70 eq47877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47877
  have eq50945 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X1 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50814 X0 X1
       have i₂ := eq66 (k X0 X0) X1
       grind)
    | exact superpose eq66 eq50814
    | (have j0 := eq50814 X0 X1
       grind)
    | exact resolve eq50814 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50814
  have eq51001 : ∀ X0 X1 : G, (M.op (τ (k X0 X0)) X1) = X1 ∨ (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50945 (τ X0) X1
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq50945
    | exact resolve eq50945 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq50945
  have eq51201 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 ∨ (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0 X1
    first
    | exact superpose eq29443 eq51001
    | (have j0 := eq51001 X0 (τ X0)
       have j1 := eq29443 X0 (τ (k X0 X0))
       grind)
    | exact resolve eq51001 eq29443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29443 eq51001
  have eq51219 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0 X1
    first
    | exact superpose eq25523 eq51201
    | (have j0 := eq51201 X0 X1
       have j1 := eq25523 X0 X1
       grind)
    | exact resolve eq51201 eq25523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25523 eq51201
  have eq51228 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29445 eq51219
    | (have j0 := eq51219 (M.op X0 X0) (τ X0)
       have j1 := eq29445 (M.op X0 X0) (τ X0)
       grind)
    | exact resolve eq51219 eq29445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29445 eq51219
  have eq56932 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq51228 X0 X1
       grind)
    | exact superpose eq51228 eq66
    | (have j1 := eq51228 X0 (τ (M.op X0 X0))
       grind)
    | exact resolve eq66 eq51228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51228
  have eq65718 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq56932 X0 (τ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56932
  have eq65719 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq65718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65718
  have eq65840 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ (M.op X0 X0))
       have i₂ := eq65719 X0
       grind)
    | exact superpose eq65719 eq9
    | exact resolve eq9 eq65719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65841 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 (τ X0) (τ (M.op X0 X0)) X2
       have i₂ := eq65719 X0
       grind)
    | exact superpose eq65719 eq64
    | exact resolve eq64 eq65719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq65719
  have eq66361 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65840 (σ X0) X1
       have i₂ := eq24038 X0 (σ X0)
       grind)
    | exact superpose eq24038 eq65840
    | (have j1 := eq24038 X0 X1
       grind)
    | exact resolve eq65840 eq24038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65840
  have eq66620 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66361 X0 X1
       have i₂ := eq66 (τ (σ X0)) X1
       grind)
    | exact superpose eq66 eq66361
    | (have j0 := eq66361 X0 X1
       grind)
    | exact resolve eq66361 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66361
  have eq66633 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66620 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66620
    | (have j0 := eq66620 X0 X1
       grind)
    | exact resolve eq66620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66620
  have eq72055 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op (τ (σ X0)) X1) (τ (σ X0)))) X2) = X2 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65841 (σ X0) X1 X2
       have i₂ := eq24038 X0 (σ X0)
       grind)
    | exact superpose eq24038 eq65841
    | (have j1 := eq24038 X0 X1
       grind)
    | exact resolve eq65841 eq24038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24038 eq65841
  have eq72407 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (τ (σ X0))) X2) = X2 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72055 X0 X1 X2
       have i₂ := eq66 (τ (σ X0)) X1
       grind)
    | exact superpose eq66 eq72055
    | (have j0 := eq72055 X0 X1 X2
       grind)
    | exact resolve eq72055 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72055
  have eq72424 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = X2 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72407 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72407
    | (have j0 := eq72407 X0 X1 X2
       grind)
    | exact resolve eq72407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72407
  have eq72657 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq72424 X1 X0 X0
       grind)
    | exact superpose eq72424 eq9
    | (have j1 := eq72424 X1 X1 x
       grind)
    | exact resolve eq9 eq72424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72424
  have eq73202 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq72657 eq24913
    | (have j0 := eq24913 X0 X1
       have j1 := eq72657 X1 X0
       grind)
    | exact resolve eq24913 eq72657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24913 eq72657
  have eq74357 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73202 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73202
    | (have j0 := eq73202 (σ X0) X1
       grind)
    | exact resolve eq73202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73202
  have eq76463 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq74357 X0 X1
       grind)
    | exact superpose eq74357 eq11
    | (have j1 := eq74357 X0 X1
       grind)
    | exact resolve eq11 eq74357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74357
  have eq76648 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (σ X0) (σ X0)
       have i₂ := eq76463 X0 X1
       grind)
    | exact superpose eq76463 eq66
    | (have j1 := eq76463 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq66 eq76463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76463
  have eq77023 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq76648 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76648
  have eq77024 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77023 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77023
  have eq77149 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq66 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq77024 X0
       grind)
    | exact superpose eq77024 eq66
    | exact resolve eq66 eq77024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77152 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ (M.op X0 X0)) (σ X0) X1
       have i₂ := eq77024 X0
       grind)
    | exact superpose eq77024 eq70
    | exact resolve eq70 eq77024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77024
  have eq105394 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30484 x
       have i₂ := eq9421
       grind)
    | exact superpose eq9421 eq30484
    | (have j0 := eq30484 x
       grind)
    | exact resolve eq30484 eq9421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9421 eq30484
  have eq105790 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq28999 x
       grind)
    | (have r₁ := eq105394
       have r₂ := eq28999 x
       grind)
    | exact resolve eq105394 eq28999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28999 eq105394
  have eq105845 : y = (M.op x x) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105790
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq105790
    | exact resolve eq105790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105790
  have eq105846 : y = (M.op x x) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by grind
  clear eq105845
  have eq105882 : y = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq66633 eq105846
    | (have j1 := eq66633 x x
       grind)
    | exact resolve eq105846 eq66633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66633 eq105846
  have eq105895 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq105882
  have eq105913 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq105895
       grind)
    | exact superpose eq105895 eq10
    | exact resolve eq10 eq105895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105895
  have eq106147 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105913
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq105913
    | exact resolve eq105913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105913
  have eq106148 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq106147
  have eq106257 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq77149 x
       have i₂ := eq106148
       grind)
    | exact superpose eq106148 eq77149
    | exact resolve eq77149 eq106148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77149
  have eq106267 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68 x x
       have i₂ := eq106148
       grind)
    | exact superpose eq106148 eq68
    | exact resolve eq68 eq106148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq106148
  have eq107493 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106257
       grind)
    | exact superpose eq106257 eq16
    | exact resolve eq16 eq106257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106257
  have eq107646 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq106267 eq107493
    | exact resolve eq107493 eq106267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106267 eq107493
  have eq107647 : x = (M.op x x) := by grind
  clear eq107646
  have eq107690 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq77152 x X0
       have i₂ := eq107647
       grind)
    | exact superpose eq107647 eq77152
    | exact resolve eq77152 eq107647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77152
  have eq107700 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq70 x x X0
       have i₂ := eq107647
       grind)
    | exact superpose eq107647 eq70
    | exact resolve eq70 eq107647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq107647
  have eq107860 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq107700 X0
       have i₂ := eq66 x X0
       grind)
    | exact superpose eq66 eq107700
    | exact resolve eq107700 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107700
  have eq107867 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq107690 X0
       have i₂ := eq66 (σ x) X0
       grind)
    | exact superpose eq66 eq107690
    | exact resolve eq107690 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq107690
  have eq108462 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107860 y
       grind)
    | exact superpose eq107860 eq16
    | exact resolve eq16 eq107860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107860
  have eq108709 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq108462
       have i₂ := eq107867 (σ y)
       grind)
    | exact superpose eq107867 eq108462
    | (have r₁ := eq108462
       have r₂ := eq107867 (σ y)
       grind)
    | exact resolve eq108462 eq107867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107867 eq108462
  have eq108931 : False := by grind
  exact eq108931

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
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
  have eq97 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq22
  have eq98 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq97
    | (have j1 := eq73 y x
       grind)
    | exact resolve eq97 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq731 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq109 eq73
    | (have j0 := eq73 (σ y) x
       grind)
    | exact resolve eq73 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq794
    | exact resolve eq794 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq798 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq795
       have r₂ := eq27
       grind)
    | exact resolve eq795 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq805 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq798 eq60
    | exact resolve eq60 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq798 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq798
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq798
       grind)
    | exact resolve eq13 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq809 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq808 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq811 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq805 x
       have i₂ := eq54 sF3 x
       grind)
    | exact superpose eq54 eq805
    | exact resolve eq805 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq819 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 y y X0
       have i₂ := eq811 X1
       grind)
    | exact superpose eq811 eq60
    | (have j1 := eq811 X1
       grind)
    | exact resolve eq60 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq825 : ∀ X0 X1 : G, (M.op (σ y) X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq819 X0 X1
       have i₂ := eq54 y X0
       grind)
    | exact superpose eq54 eq819
    | (have j0 := eq819 X0 X1
       grind)
    | exact resolve eq819 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq831 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq825 (M.op X0 X1) X1
       grind)
    | exact superpose eq825 eq54
    | (have j1 := eq825 X1 X1
       grind)
    | exact resolve eq54 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq858 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq831
    | (have j0 := eq831 (σ x) X0
       grind)
    | exact resolve eq831 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq946 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq858 y
       grind)
    | exact superpose eq858 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq858 y
       grind)
    | exact resolve eq13 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54 y X0
       have i₂ := eq858 X0
       grind)
    | exact superpose eq858 eq54
    | exact resolve eq54 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq955 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq946 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq1273 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq955 y
       grind)
    | exact superpose eq955 eq98
    | exact resolve eq98 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq955
  have eq1387 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1273
       have i₂ := eq950 y
       grind)
    | exact superpose eq950 eq1273
    | exact resolve eq1273 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950 eq1273
  have eq1401 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1387
  have eq1404 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1401
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1401
    | exact resolve eq1401 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1409 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1404 eq73
    | (have j0 := eq73 (σ y) x
       grind)
    | exact resolve eq73 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1410 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1409
  have eq1421 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1410 eq60
    | exact resolve eq60 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1430 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1421 x
       have i₂ := eq54 sF3 x
       grind)
    | exact superpose eq54 eq1421
    | exact resolve eq1421 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq1451 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1430 eq54
    | exact resolve eq54 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1531 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1451 eq26
    | (have j1 := eq1451 (σ x)
       grind)
    | exact resolve eq26 eq1451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1451
  have eq1538 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1531
  have eq1542 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1538 eq27
    | exact resolve eq27 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1544 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1538 eq56
    | exact resolve eq56 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1538
  have eq1747 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq809 eq72
    | exact resolve eq72 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq809
  have eq1753 : (τ (σ x)) = (k x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1544 eq1747
    | exact resolve eq1747 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544 eq1747
  have eq1754 : y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq1753
    | exact resolve eq1753 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1753
  have eq1758 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1754
       grind)
    | exact superpose eq1754 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1754
       grind)
    | exact resolve eq13 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1764 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq60 y y X0
       have i₂ := eq1754
       grind)
    | exact superpose eq1754 eq60
    | exact resolve eq60 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1754
  have eq1770 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq1758 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq1774 : ∀ X0 : G, x = (k x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1764 X0
       have i₂ := eq54 y X0
       grind)
    | exact superpose eq54 eq1764
    | exact resolve eq1764 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq2009 : x ≠ (M.op y x) ∨ x = (k x y) := by grind
  clear eq1770
  have eq2010 : x = (k x y) := by
    first
    | (have r₁ := eq2009
       have r₂ := eq1774 x
       grind)
    | exact resolve eq2009 eq1774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774 eq2009
  have eq2070 : x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2010
       have i₂ := eq73 x y
       grind)
    | exact superpose eq73 eq2010
    | (have j1 := eq73 x x
       grind)
    | exact resolve eq2010 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2010
  have eq2090 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq2070
       grind)
    | exact superpose eq2070 eq54
    | exact resolve eq54 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2070
  have eq2099 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2090
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2090
    | exact resolve eq2090 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2157 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq731 x
       have i₂ := eq2099
       grind)
    | exact superpose eq2099 eq731
    | exact resolve eq731 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq2099
  have eq2179 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55 eq2157
    | exact resolve eq2157 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq2157
  have eq2182 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2179
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2179
    | exact resolve eq2179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2179
  have eq2183 : y = (M.op x y) := by grind
  clear eq2182
  have eq2186 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2183 eq20
    | exact resolve eq20 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2183
  have eq2221 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2186
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2186
    | exact resolve eq2186 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2186
  have eq2223 : False := by grind
  exact eq2223

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  clear eq17
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
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq67 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq67 X1 X2 X0
       grind)
    | exact superpose eq67 eq63
    | exact resolve eq63 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1417 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq429 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq429
    | (have j0 := eq429 X1 X1
       have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq429 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1418 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq429 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq429
    | (have j0 := eq429 (σ X0) (σ X0)
       grind)
    | exact resolve eq429 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq8143 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (k X1 (σ (σ X0))) = X1 ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ (σ X0))
       have i₂ := eq1418 X0 X0
       grind)
    | exact superpose eq1418 eq12
    | (have j0 := eq12 X1 (σ (σ X0))
       have j1 := eq1418 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ (σ X0))
       have r₂ := eq1418 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ (σ X1))
       have r₂ := eq1418 X0 X1
       grind)
    | exact resolve eq12 eq1418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8231 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1418 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq8232 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq8231 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8231
  have eq8234 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (k X1 (σ (σ X0))) = X1 ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq8143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8143
  have eq8241 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (k X1 (σ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8234 X0 X1
       have j1 := eq12 X1 (σ (σ X0))
       grind)
    | (have r₁ := eq8234 X0 X1
       have r₂ := eq12 X0 (σ (σ X0))
       grind)
    | exact resolve eq8234 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8234
  have eq8259 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (k X1 (σ (σ (τ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8241 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq8241
    | (have j0 := eq8241 (τ X0) X1
       grind)
    | exact resolve eq8241 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8241
  have eq8271 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ (σ (τ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8259 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8259
    | (have j0 := eq8259 X0 X1
       grind)
    | exact resolve eq8259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8259
  have eq8278 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8271 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8271
    | (have j0 := eq8271 X0 X1
       grind)
    | exact resolve eq8271 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8271
  have eq8286 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8278 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq8278
    | (have j0 := eq8278 (τ X0) X1
       grind)
    | exact resolve eq8278 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8278
  have eq8298 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8286 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8286
    | (have j0 := eq8286 X0 X1
       grind)
    | exact resolve eq8286 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8286
  have eq8305 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8298 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8298
    | (have j0 := eq8298 X0 X1
       grind)
    | exact resolve eq8298 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8298
  have eq8311 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8305 (τ X0) X1
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq8305
    | (have j0 := eq8305 (τ X0) X1
       grind)
    | exact resolve eq8305 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8305
  have eq8334 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1417 x y
       grind)
    | exact superpose eq1417 eq16
    | (have j1 := eq1417 y y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1417 x y
       grind)
    | exact resolve eq16 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq8441 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq8334
  have eq8616 : ∀ X0 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq8232 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq8232
    | (have j0 := eq8232 (τ X0)
       grind)
    | exact resolve eq8232 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8232
  have eq8628 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq8616 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8616
    | (have j0 := eq8616 X0
       grind)
    | exact resolve eq8616 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8616
  have eq8635 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8628 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8628
    | (have j0 := eq8628 X0
       grind)
    | exact resolve eq8628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8628
  have eq8643 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8635 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq8635
    | (have j0 := eq8635 (τ X0)
       grind)
    | exact resolve eq8635 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8655 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8643 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8643
    | (have j0 := eq8643 X0
       grind)
    | exact resolve eq8643 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8643
  have eq8662 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8655 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8655
    | (have j0 := eq8655 X0
       grind)
    | exact resolve eq8655 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8655
  have eq8668 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq8662 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq8662
    | (have j0 := eq8662 (τ X0)
       grind)
    | exact resolve eq8662 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq9976 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq8441
       grind)
    | exact superpose eq8441 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq8441
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq8441
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq8441
       grind)
    | exact resolve eq12 eq8441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8441
  have eq10071 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq9976 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9976
  have eq10112 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq10071 X1
       grind)
    | exact superpose eq10071 eq12
    | (have j0 := eq12 X0 (σ x)
       have j1 := eq10071 X1
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq10071 X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq10071 X0
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq10071 X0
       grind)
    | exact resolve eq12 eq10071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10071
  have eq10207 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (k X0 (σ x)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq10112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10112
  have eq10285 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ y))) ∨ (k X1 (σ x)) = X1 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ y)
       have i₂ := eq10207 X1 (σ X0)
       grind)
    | exact superpose eq10207 eq28
    | (have j1 := eq10207 X1 X1
       grind)
    | exact resolve eq28 eq10207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10207
  have eq10358 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 y) ∨ (k X1 (σ x)) = X1 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq10285 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq10285
    | (have j0 := eq10285 X0 X1
       grind)
    | exact resolve eq10285 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10285
  have eq10383 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (k X1 (σ x)) = X1 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq10358 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10358
    | (have j0 := eq10358 X0 X1
       grind)
    | exact resolve eq10358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10358
  have eq10402 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq10383 X0 X1
       have j1 := eq12 X1 (σ x)
       grind)
    | (have r₁ := eq10383 X0 X1
       have r₂ := eq12 X0 y
       grind)
    | (have r₁ := eq10383 X0 X1
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq10383 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10383
  have eq10444 : ∀ X0 X1 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ (k X1 y) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq8311 (σ x) X0
       have i₂ := eq10402 X1 (σ x)
       grind)
    | exact superpose eq10402 eq8311
    | (have j0 := eq8311 (σ x) X0
       have j1 := eq10402 X1 X1
       grind)
    | exact resolve eq8311 eq10402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8311
  have eq10449 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (k X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8668 (σ x)
       have i₂ := eq10402 X0 (σ x)
       grind)
    | exact superpose eq10402 eq8668
    | (have j0 := eq8668 (σ x)
       have j1 := eq10402 X0 x
       grind)
    | exact resolve eq8668 eq10402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8668 eq10402
  have eq10496 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (k X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10449
  have eq10501 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (k X1 y) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq10444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10444
  have eq10533 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10496 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10496
    | (have j0 := eq10496 X0
       grind)
    | exact resolve eq10496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10496
  have eq10534 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq10533 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10533
  have eq10537 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (k X1 y) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq10501 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10501
    | (have j0 := eq10501 X0 X1
       grind)
    | exact resolve eq10501 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10501
  have eq10559 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq10537 X0 X1
       have j1 := eq12 X1 y
       grind)
    | (have r₁ := eq10537 X0 X1
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq10537 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10537
  have eq11095 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 x x X0
       have i₂ := eq10534 X1
       grind)
    | exact superpose eq10534 eq67
    | (have j1 := eq10534 X1
       grind)
    | exact resolve eq67 eq10534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10534
  have eq11220 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11095 X0 X1
       have i₂ := eq63 x X0
       grind)
    | exact superpose eq63 eq11095
    | (have j0 := eq11095 X0 X1
       grind)
    | exact resolve eq11095 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11095
  have eq11234 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq8635 y
       have i₂ := eq10559 X0 y
       grind)
    | exact superpose eq10559 eq8635
    | (have j0 := eq8635 y
       have j1 := eq10559 X0 x
       grind)
    | exact resolve eq8635 eq10559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10559
  have eq11271 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq11234 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11234
  have eq11602 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8662 y
       have i₂ := eq11220 X0 y
       grind)
    | exact superpose eq11220 eq8662
    | (have j0 := eq8662 y
       have j1 := eq11220 X0 x
       grind)
    | (have r₁ := eq8662 y
       have r₂ := eq11220 X0 y
       grind)
    | exact resolve eq8662 eq11220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8662 eq11220
  have eq11637 : ∀ X0 : G, y = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11602 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11602
  have eq12452 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 y y
       have i₂ := eq11637 X0
       grind)
    | exact superpose eq11637 eq85
    | (have j1 := eq11637 X1
       grind)
    | exact resolve eq85 eq11637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11637
  have eq12577 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12452 X1 X1
       have i₂ := eq63 y X1
       grind)
    | exact superpose eq63 eq12452
    | (have j0 := eq12452 X0 X1
       grind)
    | exact resolve eq12452 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12452
  have eq13269 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq12577 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12577
  have eq13270 : y = (M.op x y) := by grind
  clear eq13269
  have eq13335 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13270
       grind)
    | exact superpose eq13270 eq16
    | exact resolve eq16 eq13270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13270
  have eq20315 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 (σ y) (σ y)
       have i₂ := eq11271 X0
       grind)
    | exact superpose eq11271 eq85
    | (have j1 := eq11271 X1
       grind)
    | exact resolve eq85 eq11271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq11271
  have eq20458 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20315 X1 X1
       have i₂ := eq63 (σ y) X1
       grind)
    | exact superpose eq63 eq20315
    | (have j0 := eq20315 X0 X1
       grind)
    | exact resolve eq20315 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20315
  have eq20858 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq13335
       have i₂ := eq20458 (σ x) X0
       grind)
    | exact superpose eq20458 eq13335
    | (have j1 := eq20458 X0 X0
       grind)
    | (have r₁ := eq13335
       have r₂ := eq20458 (σ x) x
       grind)
    | exact resolve eq13335 eq20458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20458
  have eq20863 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq20858 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20858
  have eq21009 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8635 x
       have i₂ := eq20863 x
       grind)
    | exact superpose eq20863 eq8635
    | (have j0 := eq8635 x
       grind)
    | exact resolve eq8635 eq20863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8635 eq20863
  have eq21046 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21009
  have eq23523 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq67 (σ x) (σ x) X0
       have i₂ := eq21046
       grind)
    | exact superpose eq21046 eq67
    | exact resolve eq67 eq21046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq21046
  have eq23672 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23523 X0
       have i₂ := eq63 (σ x) X0
       grind)
    | exact superpose eq63 eq23523
    | exact resolve eq23523 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq23523
  have eq23677 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq13335
       have i₂ := eq23672 (σ y)
       grind)
    | exact superpose eq23672 eq13335
    | (have r₁ := eq13335
       have r₂ := eq23672 (σ y)
       grind)
    | exact resolve eq13335 eq23672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13335 eq23672
  have eq23805 : False := by grind
  exact eq23805
