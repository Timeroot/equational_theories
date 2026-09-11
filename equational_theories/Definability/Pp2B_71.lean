import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_y_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op X1 X0) X0
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op X1 X1) X0
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq42
    | exact resolve eq42 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq43
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq53
    | exact resolve eq53 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1574 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq105
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq105
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq105
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1575 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1574
  have eq15278 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1575
       grind)
    | exact superpose eq1575 eq16
    | exact resolve eq16 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq15279 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq15278
       have r₂ := eq22 x
       grind)
    | exact resolve eq15278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15278
  have eq54411 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45 x y
       have i₂ := eq15279
       grind)
    | exact superpose eq15279 eq45
    | exact resolve eq45 eq15279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15279
  have eq63278 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45 (σ x) (σ y)
       have i₂ := eq54411
       grind)
    | exact superpose eq54411 eq45
    | exact resolve eq45 eq54411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq54411
  have eq63298 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63278
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq63278
    | exact resolve eq63278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63278
  have eq63885 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq63298
       grind)
    | exact superpose eq63298 eq10
    | exact resolve eq10 eq63298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63298
  have eq63979 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63885
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq63885
    | exact resolve eq63885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63885
  have eq63981 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63979
       grind)
    | exact superpose eq63979 eq16
    | exact resolve eq16 eq63979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63979
  have eq63982 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq63981
       have r₂ := eq22 x
       grind)
    | exact resolve eq63981 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq63981
  have eq64398 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq63982
       grind)
    | exact superpose eq63982 eq10
    | exact resolve eq10 eq63982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63982
  have eq64494 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64398
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64398
    | exact resolve eq64398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64398
  have eq64495 : x = (M.op x x) := by grind
  clear eq64494
  have eq64500 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x
       have i₂ := eq64495
       grind)
    | exact superpose eq64495 eq53
    | exact resolve eq53 eq64495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq64501 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq81 x x
       have i₂ := eq64495
       grind)
    | exact superpose eq64495 eq81
    | exact resolve eq81 eq64495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq64495
  have eq67036 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64501 (σ y)
       grind)
    | exact superpose eq64501 eq16
    | exact resolve eq16 eq64501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64501
  have eq67348 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq67036
       have i₂ := eq64500 y
       grind)
    | exact superpose eq64500 eq67036
    | exact resolve eq67036 eq64500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64500 eq67036
  have eq67349 : False := by grind
  exact eq67349

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq108 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq108 (M.op X1 X0) X0
       have i₂ := eq108 X0 X1
       grind)
    | exact superpose eq108 eq108
    | exact resolve eq108 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq109
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq108 (M.op X1 X1) X0
       have i₂ := eq109 X1 X0
       grind)
    | exact superpose eq109 eq108
    | exact resolve eq108 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq133 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq108 (σ (M.op X1 X1)) X0
       have i₂ := eq117 X1 X0
       grind)
    | exact superpose eq117 eq108
    | exact resolve eq108 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq117
  have eq1375 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
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
  have eq1376 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq4734 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1376 x y
       grind)
    | exact superpose eq1376 eq16
    | (have j1 := eq1376 x y
       grind)
    | exact resolve eq16 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq12099 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1375 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1375
    | exact resolve eq1375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq12183 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12099 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12099
    | (have j0 := eq12099 X0 X1
       grind)
    | exact resolve eq12099 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12099
  have eq22665 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq4734
       have i₂ := eq12183 y x
       grind)
    | exact superpose eq12183 eq4734
    | (have j1 := eq12183 (σ y) (σ x)
       grind)
    | (have r₁ := eq4734
       have r₂ := eq12183 y x
       grind)
    | (have r₁ := eq4734
       have r₂ := eq12183 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4734
       have r₂ := eq12183 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4734 eq12183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4734 eq12183
  have eq22666 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq22665
  have eq2182308 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22666
       grind)
    | exact superpose eq22666 eq16
    | exact resolve eq16 eq22666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22666
  have eq2182359 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq2182308
       have r₂ := eq22 x
       grind)
    | exact resolve eq2182308 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182308
  have eq2182451 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113 x y
       have i₂ := eq2182359
       grind)
    | exact superpose eq2182359 eq113
    | exact resolve eq113 eq2182359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182359
  have eq2182699 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113 (σ x) (σ y)
       have i₂ := eq2182451
       grind)
    | exact superpose eq2182451 eq113
    | exact resolve eq113 eq2182451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq2182451
  have eq2183084 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2182699
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq2182699
    | exact resolve eq2182699 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182699
  have eq2183207 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2183084
       grind)
    | exact superpose eq2183084 eq10
    | exact resolve eq10 eq2183084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183084
  have eq2183620 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2183207
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2183207
    | exact resolve eq2183207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183207
  have eq2183622 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2183620
       grind)
    | exact superpose eq2183620 eq16
    | exact resolve eq16 eq2183620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183620
  have eq2183648 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2183622
       have r₂ := eq22 x
       grind)
    | exact resolve eq2183622 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2183622
  have eq2184155 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2183648
       grind)
    | exact superpose eq2183648 eq10
    | exact resolve eq10 eq2183648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183648
  have eq2184577 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2184155
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2184155
    | exact resolve eq2184155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184155
  have eq2184578 : x = (M.op x x) := by grind
  clear eq2184577
  have eq2184587 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq123 X0 x
       have i₂ := eq2184578
       grind)
    | exact superpose eq2184578 eq123
    | exact resolve eq123 eq2184578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq2184589 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq133 X0 x
       have i₂ := eq2184578
       grind)
    | exact superpose eq2184578 eq133
    | exact resolve eq133 eq2184578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq2184578
  have eq2203806 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2184589 (σ y)
       grind)
    | exact superpose eq2184589 eq16
    | exact resolve eq16 eq2184589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184589
  have eq2206759 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2203806
       have i₂ := eq2184587 y
       grind)
    | exact superpose eq2184587 eq2203806
    | exact resolve eq2203806 eq2184587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184587 eq2203806
  have eq2206760 : False := by grind
  exact eq2206760

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  clear eq18
  have eq42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op X1 X0) X0
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) X0
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq13
    | (have j0 := eq13 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X1 X0) X0
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq13 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq45 X0 X1
       grind)
    | exact resolve eq13 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq70 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq113 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq42
    | (have j1 := eq83 X0 X1
       grind)
    | exact resolve eq42 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq141 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq1802 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq113
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq113
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq113
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq113
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq113 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1803 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1802
  have eq1940 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (σ X1) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 (M.op X0 X1) X1
       have i₂ := eq58 X1 X0
       grind)
    | exact superpose eq58 eq117
    | (have j0 := eq117 (M.op X0 X1) X1
       have j1 := eq58 X1 X0
       grind)
    | exact resolve eq117 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1944 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq117 (τ X0) (τ X1)
       have i₂ := eq141 X1 X0
       grind)
    | exact superpose eq141 eq117
    | (have j0 := eq117 (τ X0) (τ X1)
       grind)
    | exact resolve eq117 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq141
  have eq1957 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (σ X1) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1940 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq1969 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1944 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1944
    | (have j0 := eq1944 X0 X1
       grind)
    | exact resolve eq1944 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq1974 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1969 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1969
    | (have j0 := eq1969 X0 X1
       grind)
    | exact resolve eq1969 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq1976 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1974 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1974
    | (have j0 := eq1974 X0 X1
       grind)
    | exact resolve eq1974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq1977 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1976 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1976
    | (have j0 := eq1976 X0 X1
       grind)
    | exact resolve eq1976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq1978 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1977 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1977
    | (have j0 := eq1977 X0 X1
       grind)
    | exact resolve eq1977 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq1979 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1978 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1978
    | (have j0 := eq1978 X0 X1
       grind)
    | exact resolve eq1978 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1978
  have eq13515 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1803
       grind)
    | exact superpose eq1803 eq16
    | exact resolve eq16 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq13516 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq13515
       have r₂ := eq22 x
       grind)
    | exact resolve eq13515 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13515
  have eq24462 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq42 x y
       have i₂ := eq13516
       grind)
    | exact superpose eq13516 eq42
    | exact resolve eq42 eq13516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13516
  have eq31986 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1957 x y
       have i₂ := eq24462
       grind)
    | exact superpose eq24462 eq1957
    | exact resolve eq1957 eq24462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957 eq24462
  have eq31997 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq31986
  have eq32208 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31997
       grind)
    | exact superpose eq31997 eq16
    | exact resolve eq16 eq31997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31997
  have eq32209 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq32208
       have r₂ := eq22 x
       grind)
    | exact resolve eq32208 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32208
  have eq32224 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42 (σ x) (σ y)
       have i₂ := eq32209
       grind)
    | exact superpose eq32209 eq42
    | exact resolve eq42 eq32209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32227 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70 (σ y) (σ x)
       have i₂ := eq32209
       grind)
    | exact superpose eq32209 eq70
    | exact resolve eq70 eq32209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq32209
  have eq32250 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq32227
  have eq32277 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq32250
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq32250
    | exact resolve eq32250 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32250
  have eq32855 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq32277
       grind)
    | exact superpose eq32277 eq10
    | exact resolve eq10 eq32277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32277
  have eq32950 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq32855
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq32855
    | exact resolve eq32855 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32855
  have eq32952 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32950
       grind)
    | exact superpose eq32950 eq16
    | exact resolve eq16 eq32950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32950
  have eq32953 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq32952
       have r₂ := eq22 x
       grind)
    | exact resolve eq32952 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32952
  have eq33330 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq32953
       grind)
    | exact superpose eq32953 eq10
    | exact resolve eq10 eq32953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32953
  have eq33427 : x = (k x y) := by
    first
    | (have i₁ := eq33330
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33330
    | exact resolve eq33330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33330
  have eq33438 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1979 x y
       have i₂ := eq33427
       grind)
    | exact superpose eq33427 eq1979
    | (have j0 := eq1979 x y
       grind)
    | exact resolve eq1979 eq33427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979 eq33427
  have eq33443 : x = y ∨ y = (M.op y x) := by grind
  clear eq33438
  have eq33719 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33443
       grind)
    | exact superpose eq33443 eq16
    | exact resolve eq16 eq33443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33443
  have eq33724 : y = (M.op y x) := by
    first
    | (have r₁ := eq33719
       have r₂ := eq22 x
       grind)
    | exact resolve eq33719 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33719
  have eq33730 : x = (M.op x y) := by
    first
    | (have i₁ := eq42 x y
       have i₂ := eq33724
       grind)
    | exact superpose eq33724 eq42
    | exact resolve eq42 eq33724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq33724
  have eq37970 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32224
       grind)
    | exact superpose eq32224 eq16
    | exact resolve eq16 eq32224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32224
  have eq38043 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37970
       have i₂ := eq33730
       grind)
    | exact superpose eq33730 eq37970
    | exact resolve eq37970 eq33730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33730 eq37970
  have eq38044 : (σ x) = (σ y) := by grind
  clear eq38043
  have eq38050 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq38044
       grind)
    | exact superpose eq38044 eq10
    | exact resolve eq10 eq38044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38044
  have eq38145 : x = y := by
    first
    | (have i₁ := eq38050
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38050
    | exact resolve eq38050 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38050
  have eq38730 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38145
       grind)
    | exact superpose eq38145 eq16
    | exact resolve eq16 eq38145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38145
  have eq38762 : False := by grind
  exact eq38762

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op X1 X0) X0
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq43
    | exact resolve eq43 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op X1 X1) X0
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq43
    | exact resolve eq43 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq44
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq92 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq54
    | exact resolve eq54 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq162 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 x y
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq2757 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq162
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq162
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq162
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq162
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq162 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq2758 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2757
  have eq15658 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2758
       grind)
    | exact superpose eq2758 eq16
    | exact resolve eq16 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758
  have eq15659 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq15658
       have r₂ := eq23 x
       grind)
    | exact resolve eq15658 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15658
  have eq35664 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15659
       grind)
    | exact superpose eq15659 eq10
    | exact resolve eq10 eq15659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15659
  have eq35760 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq35664
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35664
    | exact resolve eq35664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35664
  have eq36110 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35760
       grind)
    | exact superpose eq35760 eq16
    | exact resolve eq16 eq35760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35760
  have eq36111 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq36110
       have r₂ := eq23 x
       grind)
    | exact resolve eq36110 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq36110
  have eq36155 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq36111
       grind)
    | exact superpose eq36111 eq10
    | exact resolve eq10 eq36111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36111
  have eq36285 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq36155
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq36155
    | exact resolve eq36155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36155
  have eq36286 : x = (M.op y y) := by grind
  clear eq36285
  have eq36658 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq92 y x
       have i₂ := eq36286
       grind)
    | exact superpose eq36286 eq92
    | exact resolve eq92 eq36286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq36811 : x = (M.op x y) := by
    first
    | (have i₁ := eq46 y y
       have i₂ := eq36286
       grind)
    | exact superpose eq36286 eq46
    | exact resolve eq46 eq36286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq36286
  have eq38585 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36658 (σ y)
       grind)
    | exact superpose eq36658 eq16
    | exact resolve eq16 eq36658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36658
  have eq38797 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq38585
       have i₂ := eq36811
       grind)
    | exact superpose eq36811 eq38585
    | exact resolve eq38585 eq36811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36811 eq38585
  have eq38798 : False := by grind
  exact eq38798

/-- `Equation439`: `x = x ◇ (y ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation439 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law439 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law439.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X0)))) = X0 := by
    intro X0 X1
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  have eq56 : y = (M.op y (M.op x (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq81
    | exact resolve eq81 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq93 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
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
  have eq859 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq9156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq9157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9156
    | exact resolve eq9156 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9156
  have eq9168 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq9157
       have r₂ := eq27
       grind)
    | exact resolve eq9157 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9157
  have eq9170 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9168
    | exact resolve eq9168 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9168
  have eq9182 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9170 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9170
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9170
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9170
       grind)
    | exact resolve eq13 eq9170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9170
  have eq9188 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq9182
  have eq9197 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9188 eq55
    | exact resolve eq55 eq9188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq9188
  have eq9222 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq9197
    | exact resolve eq9197 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9197
  have eq9225 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq9222
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq9222
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq9222
       have r₂ := eq13 x y
       grind)
    | exact resolve eq9222 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9222
  have eq9244 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq859 x y
       have i₂ := eq9225
       grind)
    | exact superpose eq9225 eq859
    | (have j0 := eq859 x y
       grind)
    | exact resolve eq859 eq9225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9246 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq9225
       grind)
    | exact superpose eq9225 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq9225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9225
  have eq9247 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9246
  have eq9249 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9244
  have eq9252 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9247
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9247
    | exact resolve eq9247 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9247
  have eq9253 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9252
  have eq9255 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9249
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9249
    | exact resolve eq9249 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9249
  have eq9267 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9255
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9255
    | exact resolve eq9255 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9255
  have eq9270 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9267
    | exact resolve eq9267 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9267
  have eq9271 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9270
  have eq9274 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9271
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9271
    | exact resolve eq9271 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9271
  have eq9277 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9274
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9274
    | exact resolve eq9274 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9274
  have eq9278 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq9253
       grind)
    | exact superpose eq9253 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9253
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9253
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9253
       grind)
    | exact resolve eq12 eq9253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9253
  have eq9286 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9278
  have eq9287 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9286
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9286
    | exact resolve eq9286 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9286
  have eq9288 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9287
  have eq9289 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9288
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9288
    | exact resolve eq9288 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9288
  have eq10263 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9277 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9277
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9277
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9277
       grind)
    | exact resolve eq12 eq9277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9277
  have eq10271 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10263
  have eq10272 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10271
    | exact resolve eq10271 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10271
  have eq10273 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq10272
  have eq10274 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10273
    | exact resolve eq10273 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10273
  have eq10276 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq9289
       grind)
    | exact superpose eq9289 eq91
    | exact resolve eq91 eq9289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9289
  have eq10298 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10276
    | exact resolve eq10276 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10276
  have eq10490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10298 eq10274
    | exact resolve eq10274 eq10298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10274 eq10298
  have eq10496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10490
  have eq10498 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10496
       have r₂ := eq27
       grind)
    | exact resolve eq10496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10496
  have eq10508 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10498 eq51
    | (have r₁ := eq51
       have r₂ := eq10498
       grind)
    | exact resolve eq51 eq10498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq10498
  have eq10517 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq10508
  have eq10568 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10517 eq101
    | exact resolve eq101 eq10517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq10517
  have eq10598 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq10568
    | exact resolve eq10568 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10568
  have eq10600 : y = (k y x) := by
    first
    | (have r₁ := eq10598
       have r₂ := eq50
       grind)
    | exact resolve eq10598 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq10598
  have eq10603 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq10600
       grind)
    | exact superpose eq10600 eq91
    | exact resolve eq91 eq10600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10613 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq859 y x
       have i₂ := eq10600
       grind)
    | exact superpose eq10600 eq859
    | (have j0 := eq859 y x
       grind)
    | exact resolve eq859 eq10600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq10615 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq10600
       grind)
    | exact superpose eq10600 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq10600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10616 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq10615
  have eq10618 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10613
  have eq10621 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10616
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10616
    | exact resolve eq10616 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10616
  have eq10623 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10618
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10618
    | exact resolve eq10618 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10618
  have eq10632 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10603
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10603
    | exact resolve eq10603 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10603
  have eq10635 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10623
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10623
    | exact resolve eq10623 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10623
  have eq10639 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10635
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10635
    | exact resolve eq10635 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10635
  have eq10643 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10639
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10639
    | exact resolve eq10639 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10639
  have eq10647 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10643
    | exact resolve eq10643 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10643
  have eq11022 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq10621
       grind)
    | exact superpose eq10621 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10621
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq10621
       grind)
    | exact resolve eq12 eq10621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11024 : x = (M.op x (M.op y (M.op y y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq10621
       grind)
    | exact superpose eq10621 eq14
    | exact resolve eq14 eq10621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10621
  have eq11031 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq11022
  have eq11032 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11031
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11031
    | exact resolve eq11031 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11031
  have eq11033 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq11032
  have eq11034 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11033
       have i₂ := eq10600
       grind)
    | exact superpose eq10600 eq11033
    | exact resolve eq11033 eq10600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10600 eq11033
  have eq11035 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11034
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11034
    | exact resolve eq11034 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11034
  have eq11366 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11035 eq56
    | exact resolve eq56 eq11035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq11424 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq11479 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11366
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11366
    | exact resolve eq11366 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11366
  have eq17163 : y = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq11035 eq11479
    | exact resolve eq11479 eq11035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11479
  have eq17177 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17163
       have r₂ := eq11424
       grind)
    | exact resolve eq17163 eq11424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17163
  have eq17178 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17177
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17177
    | exact resolve eq17177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17177
  have eq17179 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq11035 eq17178
    | exact resolve eq17178 eq11035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11035 eq17178
  have eq17193 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17179
       have r₂ := eq11424
       grind)
    | exact resolve eq17179 eq11424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11424 eq17179
  have eq29005 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11024
       have i₂ := eq17193
       grind)
    | exact superpose eq17193 eq11024
    | exact resolve eq11024 eq17193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11024
  have eq29021 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq29005
  have eq29022 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29021
       have i₂ := eq17193
       grind)
    | exact superpose eq17193 eq29021
    | exact resolve eq29021 eq17193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17193 eq29021
  have eq29038 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq29022
  have eq29039 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29038
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29038
    | exact resolve eq29038 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq29038
  have eq29040 : x = (M.op x y) := by grind
  clear eq29039
  have eq29042 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq29040 eq20
    | exact resolve eq20 eq29040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq29048 : (σ (k y x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq29040 eq93
    | exact resolve eq93 eq29040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq29040
  have eq29173 : (k (σ y) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29048
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq29048
    | exact resolve eq29048 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq29048
  have eq29177 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq29042
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29042
    | exact resolve eq29042 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29042
  have eq29188 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq10632 eq29173
    | exact resolve eq29173 eq10632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10632 eq29173
  have eq29194 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq29177 eq26
    | exact resolve eq26 eq29177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29274 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29177 eq10647
    | exact resolve eq10647 eq29177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10647 eq29177
  have eq29307 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq29274
       have r₂ := eq27
       grind)
    | exact resolve eq29274 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29274
  have eq29430 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq29307 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq29307
       grind)
    | exact resolve eq12 eq29307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29432 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq29307 eq14
    | exact resolve eq14 eq29307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29307
  have eq29443 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq29430
  have eq29444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq29194 eq29443
    | exact resolve eq29443 eq29194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29443
  have eq29445 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq29444
       have r₂ := eq27
       grind)
    | exact resolve eq29444 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29444
  have eq29446 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq29194 eq29445
    | exact resolve eq29445 eq29194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29445
  have eq29447 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29188 eq29446
    | exact resolve eq29446 eq29188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29188 eq29446
  have eq29451 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq29447 eq57
    | exact resolve eq57 eq29447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq29475 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq29451
    | exact resolve eq29451 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29451
  have eq29485 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29447 eq29475
    | exact resolve eq29475 eq29447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29475
  have eq29494 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq29485
    | exact resolve eq29485 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq29485
  have eq29501 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq29447 eq29494
    | exact resolve eq29494 eq29447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29447 eq29494
  have eq32549 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq29501 eq29432
    | exact resolve eq29432 eq29501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29432
  have eq32550 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq29501 eq32549
    | exact resolve eq32549 eq29501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29501 eq32549
  have eq32551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29194 eq32550
    | exact resolve eq32550 eq29194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29194 eq32550
  have eq32552 : False := by grind
  exact eq32552

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_y_pyx_Equation4393 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
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
  have eq176 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 (M.op x X3) X3
       have i₂ := eq16 X0 x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq176 x X1 X3
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq176
    | exact resolve eq176 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq182 : ∀ X3 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X3
    first
    | (have i₁ := eq180 x X3
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq180
    | exact resolve eq180 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq189 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op x y) y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 x X1 X2
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq178
  have eq206 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq195 eq182
    | exact resolve eq182 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq182 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 x (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq182 x
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | (have j0 := eq216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq220 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq195 eq218
    | exact resolve eq218 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq250 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | (have i₁ := eq189 X0 X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq189
    | exact resolve eq189 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq251 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) ≠ X0 ∨ (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq13
    | exact resolve eq13 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq182 (M.op sF4 sF3)
       have i₂ := eq220 (M.op sF4 sF3)
       grind)
    | exact superpose eq220 eq182
    | exact resolve eq182 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq195 eq253
    | exact resolve eq253 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq472 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq901 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq11
    | exact resolve eq11 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq901 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq1004 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq968 X0
       have j1 := eq251 X0
       grind)
    | (have r₁ := eq968 X0
       have r₂ := eq251 X0
       grind)
    | exact resolve eq968 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq968
  have eq1068 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq250 (M.op sF0 y)
       have i₂ := eq1004 (M.op sF0 y)
       grind)
    | exact superpose eq1004 eq250
    | exact resolve eq250 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq1070 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq220 (M.op sF0 y)
       have i₂ := eq1004 (M.op sF0 y)
       grind)
    | exact superpose eq1004 eq220
    | exact resolve eq220 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1082 : ∀ X0 : G, (τ (k (σ X0) (M.op (M.op x y) y))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq472 X0 (σ X0)
       have i₂ := eq1004 (σ X0)
       grind)
    | (have i₁ := eq472 X0 (M.op (M.op x y) y)
       have i₂ := eq1004 (σ X0)
       grind)
    | exact superpose eq1004 eq472
    | exact resolve eq472 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1086 : ∀ X0 : G, (k X0 X0) = (τ (k (σ X0) (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq1082 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1082
    | exact resolve eq1082 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1099 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq1086 X0
       have i₂ := eq472 X0 (M.op sF0 y)
       grind)
    | exact superpose eq472 eq1086
    | exact resolve eq1086 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1156 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1068 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1068
    | exact resolve eq1068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1666 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq257 eq1156
    | exact resolve eq1156 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1726 : (M.op (M.op x y) y) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq1666
       have i₂ := eq220 (σ (M.op sF0 y))
       grind)
    | exact superpose eq220 eq1666
    | exact resolve eq1666 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq1666
  have eq2469 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq914
       grind)
    | exact superpose eq914 eq39
    | exact resolve eq39 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq914
  have eq2470 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2469
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2469
    | exact resolve eq2469 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469
  have eq2472 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2470
    | exact resolve eq2470 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470
  have eq2474 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2472
       have i₂ := eq1070 y
       grind)
    | exact superpose eq1070 eq2472
    | exact resolve eq2472 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472
  have eq3397 : (τ (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq1726 eq472
    | exact resolve eq472 eq1726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq1726
  have eq3402 : (k (M.op (M.op x y) y) (M.op (M.op x y) y)) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq1099 eq3397
    | exact resolve eq3397 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099 eq3397
  have eq3405 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq257 eq3402
    | exact resolve eq3402 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq3402
  have eq3420 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3405 eq14
    | exact resolve eq14 eq3405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2474 eq915
    | exact resolve eq915 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq2474
  have eq4155 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4146
       have r₂ := eq27
       grind)
    | exact resolve eq4146 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4146
  have eq4160 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4155
       have i₂ := eq1070 sF3
       grind)
    | exact superpose eq1070 eq4155
    | exact resolve eq4155 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq4155
  have eq4162 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4160 eq115
    | exact resolve eq115 eq4160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq4160
  have eq4182 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4162
    | exact resolve eq4162 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4162
  have eq4183 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4182
  have eq4195 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1068 y
       have i₂ := eq4183
       grind)
    | exact superpose eq4183 eq1068
    | exact resolve eq1068 eq4183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq4198 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1156 y
       have i₂ := eq4183
       grind)
    | exact superpose eq4183 eq1156
    | exact resolve eq1156 eq4183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156 eq4183
  have eq4206 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4198
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4198
    | exact resolve eq4198 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4198
  have eq4207 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4195
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4195
    | exact resolve eq4195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4195
  have eq4213 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4206
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4206
    | exact resolve eq4206 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4206
  have eq4218 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4213
    | exact resolve eq4213 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213
  have eq4219 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4207 eq4218
    | exact resolve eq4218 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4218
  have eq4221 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4219 eq182
    | exact resolve eq182 eq4219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq4222 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4219 eq195
    | exact resolve eq195 eq4219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4224 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq4226 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4222
    | exact resolve eq4222 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4222
  have eq4227 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq4221
    | (have j0 := eq4221 X0
       grind)
    | exact resolve eq4221 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4221
  have eq4229 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4219 eq4226
    | exact resolve eq4226 eq4219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq4230 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4219 eq4227
    | exact resolve eq4227 eq4219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4219 eq4227
  have eq4350 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4207 eq3420
    | exact resolve eq3420 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4207
  have eq4359 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4350
    | exact resolve eq4350 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4350
  have eq4481 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4359 eq195
    | exact resolve eq195 eq4359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq4483 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4481
    | exact resolve eq4481 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4481
  have eq4487 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4359 eq4483
    | exact resolve eq4483 eq4359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4483
  have eq4960 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4229 eq3405
    | exact resolve eq3405 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4229
  have eq4980 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4960
    | exact resolve eq4960 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4960
  have eq5109 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4980 eq27
    | exact resolve eq27 eq4980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4980
  have eq5417 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4487 eq3405
    | exact resolve eq3405 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3405 eq4487
  have eq5438 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq5417
    | exact resolve eq5417 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5417
  have eq5480 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5438
       have r₂ := eq5109
       grind)
    | exact resolve eq5438 eq5109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5109 eq5438
  have eq5520 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5480
       grind)
    | exact superpose eq5480 eq18
    | exact resolve eq18 eq5480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5532 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq5480
  have eq5880 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5520 eq4230
    | exact resolve eq4230 eq5520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4230 eq5520
  have eq5888 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5880
  have eq5892 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5888
       have r₂ := eq4224
       grind)
    | exact resolve eq5888 eq4224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4224 eq5888
  have eq5898 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5892 eq27
    | exact resolve eq27 eq5892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5903 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5892 eq4359
    | exact resolve eq4359 eq5892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4359 eq5892
  have eq5904 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5903
  have eq5907 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5904
       have r₂ := eq5532
       grind)
    | exact resolve eq5904 eq5532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5532 eq5904
  have eq5910 : x = (M.op x y) := by
    first
    | (have r₁ := eq5907
       have r₂ := eq5898
       grind)
    | exact resolve eq5907 eq5898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898 eq5907
  have eq5913 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5910
       grind)
    | exact superpose eq5910 eq18
    | exact resolve eq18 eq5910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5914 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5910
       grind)
    | exact superpose eq5910 eq22
    | exact resolve eq22 eq5910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5910
  have eq6069 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq5913 eq206
    | exact resolve eq206 eq5913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq6114 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5913 eq3420
    | exact resolve eq3420 eq5913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420 eq5913
  have eq6228 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq6114 eq5914
    | exact resolve eq5914 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5914
  have eq6229 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq6114 eq20
    | exact resolve eq20 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6114
  have eq6276 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq6228 eq26
    | exact resolve eq26 eq6228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6228
  have eq6320 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6069 eq6276
    | exact resolve eq6276 eq6069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6069 eq6276
  have eq6393 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq6320 eq27
    | exact resolve eq27 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6320
  have eq6403 : False := by grind
  exact eq6403

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pyx_Equation4393 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
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
  have eq174 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X4) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq16 x X3 X4
       have i₂ := eq16 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 (M.op x X3) X3
       have i₂ := eq16 X0 x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq176 x X1 X3
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq176
    | exact resolve eq176 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq182 : ∀ X3 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X3
    first
    | (have i₁ := eq180 x X3
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq180
    | exact resolve eq180 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op x y) y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 x X1 X2
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq198 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq189 eq182
    | exact resolve eq182 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq182 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq182 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | (have j0 := eq205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq214 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq189 eq210
    | exact resolve eq210 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq244 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq182 (M.op sF4 sF3)
       have i₂ := eq214 (M.op sF4 sF3)
       grind)
    | exact superpose eq214 eq182
    | exact resolve eq182 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq189 eq244
    | exact resolve eq244 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq914 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq214 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq214
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq945 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq952 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq1829 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq934
       grind)
    | exact superpose eq934 eq39
    | exact resolve eq39 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1830 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1829
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1829
    | exact resolve eq1829 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq1832 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1830
    | exact resolve eq1830 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830
  have eq11235 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq214 (M.op sF0 y)
       have i₂ := eq952 (M.op sF0 y)
       grind)
    | exact superpose eq952 eq214
    | (have j1 := eq952 X0
       grind)
    | exact resolve eq214 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq11343 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11235 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq11235 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq11235 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11235
  have eq11430 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq11343 X0
       grind)
    | exact superpose eq11343 eq177
    | exact resolve eq177 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq11436 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq214 X0
       have i₂ := eq11343 X0
       grind)
    | exact superpose eq11343 eq214
    | exact resolve eq214 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11449 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq184 X0 X0
       have i₂ := eq11343 X0
       grind)
    | exact superpose eq11343 eq184
    | exact resolve eq184 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11496 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11430 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq11430
    | exact resolve eq11430 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11430
  have eq11572 : ∀ X0 : G, (k (σ X0) (M.op (M.op x y) y)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq11436 (σ X0)
       grind)
    | exact superpose eq11436 eq10
    | exact resolve eq10 eq11436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11436
  have eq11835 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11449 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq11449
    | exact resolve eq11449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13648 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq248 eq11496
    | exact resolve eq11496 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11496
  have eq13725 : (M.op (M.op x y) y) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq13648
       have i₂ := eq214 (σ (M.op sF0 y))
       grind)
    | exact superpose eq214 eq13648
    | exact resolve eq13648 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq13648
  have eq14285 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq248 eq11572
    | exact resolve eq11572 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq11572
  have eq14546 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq13725 eq14285
    | exact resolve eq14285 eq13725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13725 eq14285
  have eq31217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1832 eq945
    | exact resolve eq945 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq1832
  have eq31224 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq31217
       have r₂ := eq27
       grind)
    | exact resolve eq31217 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31217
  have eq31230 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq31224
       have i₂ := eq11343 sF3
       grind)
    | exact superpose eq11343 eq31224
    | exact resolve eq31224 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31224
  have eq31234 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq31230
       have i₂ := eq11343 sF2
       grind)
    | exact superpose eq11343 eq31230
    | exact resolve eq31230 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31230
  have eq31238 : x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq31234
       have i₂ := eq11343 y
       grind)
    | exact superpose eq11343 eq31234
    | exact resolve eq31234 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31234
  have eq31240 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq31238
       have i₂ := eq11343 x
       grind)
    | exact superpose eq11343 eq31238
    | exact resolve eq31238 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31238
  have eq31245 : (τ (σ x)) = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq31240 eq115
    | exact resolve eq115 eq31240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq31240
  have eq31280 : x = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq31245
    | exact resolve eq31245 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31245
  have eq31281 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by grind
  clear eq31280
  have eq31300 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq31281 eq141
    | exact resolve eq141 eq31281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq31281
  have eq31342 : x = (k x x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq31300
    | exact resolve eq31300 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31300
  have eq31343 : x = (k y y) ∨ x = (k x x) := by grind
  clear eq31342
  have eq31382 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq11449 y
       have i₂ := eq31343
       grind)
    | exact superpose eq31343 eq11449
    | exact resolve eq11449 eq31343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31385 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq11835 y
       have i₂ := eq31343
       grind)
    | exact superpose eq31343 eq11835
    | exact resolve eq11835 eq31343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31343
  have eq31393 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq31385
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31385
    | exact resolve eq31385 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31385
  have eq31395 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq31382
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31382
    | exact resolve eq31382 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31382
  have eq31408 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq31393
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31393
    | exact resolve eq31393 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31393
  have eq31418 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | exact superpose eq26 eq31408
    | exact resolve eq31408 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31408
  have eq31423 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31395 eq31418
    | exact resolve eq31418 eq31395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31418
  have eq31433 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq31423
       grind)
    | exact superpose eq31423 eq39
    | exact resolve eq39 eq31423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31444 : (M.op (M.op x y) y) = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11449 x
       have i₂ := eq31423
       grind)
    | exact superpose eq31423 eq11449
    | exact resolve eq11449 eq31423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31447 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11835 x
       have i₂ := eq31423
       grind)
    | exact superpose eq31423 eq11835
    | exact resolve eq11835 eq31423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31462 : (M.op (M.op x y) y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31447
       have i₂ := eq11343 (σ x)
       grind)
    | exact superpose eq11343 eq31447
    | exact resolve eq31447 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31447
  have eq31465 : (k x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31444
       have i₂ := eq11343 x
       grind)
    | exact superpose eq11343 eq31444
    | exact resolve eq31444 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31444
  have eq31474 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31433
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31433
    | exact resolve eq31433 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31433
  have eq31483 : (σ (k x x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31462
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq31462
    | exact resolve eq31462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31462
  have eq31486 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31423 eq31465
    | exact resolve eq31465 eq31423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31423 eq31465
  have eq31498 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31483
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq31483
    | exact resolve eq31483 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31483
  have eq31507 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31498
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31498
    | exact resolve eq31498 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31498
  have eq31515 : x = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31486 eq31507
    | exact resolve eq31507 eq31486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31507
  have eq31521 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq31474 eq31515
    | exact resolve eq31515 eq31474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31515
  have eq32271 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31474 eq11449
    | exact resolve eq11449 eq31474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32292 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32271
       have i₂ := eq11343 sF2
       grind)
    | exact superpose eq11343 eq32271
    | exact resolve eq32271 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32271
  have eq32315 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31474 eq32292
    | exact resolve eq32292 eq31474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31474 eq32292
  have eq32354 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31486 eq198
    | exact resolve eq198 eq31486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq32425 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq31486 eq174
    | exact resolve eq174 eq31486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31486
  have eq32430 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32425 x x
       have i₂ := eq184 x x
       grind)
    | (have i₁ := eq32425 x y
       have i₂ := eq184 x x
       grind)
    | exact superpose eq184 eq32425
    | (have j0 := eq32425 x y
       grind)
    | exact resolve eq32425 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32425
  have eq32496 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31521 eq32354
    | exact resolve eq32354 eq31521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31521 eq32354
  have eq32501 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32430
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32430
    | exact resolve eq32430 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32430
  have eq32769 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32496 eq26
    | (have j1 := eq32496 (σ y)
       grind)
    | exact resolve eq26 eq32496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq32496
  have eq32848 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq32769
  have eq32928 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32501 eq32315
    | exact resolve eq32315 eq32501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32315 eq32501
  have eq32935 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq32928
  have eq32940 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32935
       have r₂ := eq32848
       grind)
    | exact resolve eq32935 eq32848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32848 eq32935
  have eq32989 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq32940 eq27
    | exact resolve eq27 eq32940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32990 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq32940 eq182
    | exact resolve eq182 eq32940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq32991 : (M.op (M.op x y) y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq32940 eq189
    | exact resolve eq189 eq32940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq32940
  have eq33120 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op x y) (σ y)) y) := by
    intro X0 X1
    first
    | exact superpose eq32991 eq174
    | exact resolve eq174 eq32991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq33124 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq32990 eq33120
    | exact resolve eq33120 eq32990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32990 eq33120
  have eq34251 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (M.op x y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq33124 X0 X0
       have i₂ := eq11343 X0
       grind)
    | exact superpose eq11343 eq33124
    | exact resolve eq33124 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33124
  have eq35313 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq31395 eq14546
    | exact resolve eq14546 eq31395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14546 eq31395
  have eq35336 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq35313
    | exact resolve eq35313 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35313
  have eq35377 : x = (k x x) := by
    first
    | (have r₁ := eq35336
       have r₂ := eq32989
       grind)
    | exact resolve eq35336 eq32989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35336
  have eq35400 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq35377
       grind)
    | exact superpose eq35377 eq39
    | exact resolve eq39 eq35377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35412 : (M.op (M.op x y) y) = (M.op x x) := by
    first
    | (have i₁ := eq11449 x
       have i₂ := eq35377
       grind)
    | exact superpose eq35377 eq11449
    | exact resolve eq11449 eq35377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11449
  have eq35415 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11835 x
       have i₂ := eq35377
       grind)
    | exact superpose eq35377 eq11835
    | exact resolve eq11835 eq35377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11835
  have eq35422 : (M.op x x) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq34251 x
       have i₂ := eq35377
       grind)
    | exact superpose eq35377 eq34251
    | exact resolve eq34251 eq35377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34251
  have eq35427 : (k x x) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq35422
       have i₂ := eq11343 x
       grind)
    | exact superpose eq11343 eq35422
    | exact resolve eq35422 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35422
  have eq35434 : (M.op (M.op x y) y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35415
       have i₂ := eq11343 (σ x)
       grind)
    | exact superpose eq11343 eq35415
    | exact resolve eq35415 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35415
  have eq35437 : (k x x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq35412
       have i₂ := eq11343 x
       grind)
    | exact superpose eq11343 eq35412
    | exact resolve eq35412 eq11343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11343 eq35412
  have eq35446 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35400
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35400
    | exact resolve eq35400 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35400
  have eq35450 : x = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq35427
       have i₂ := eq35377
       grind)
    | exact superpose eq35377 eq35427
    | exact resolve eq35427 eq35377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35427
  have eq35457 : (σ (k x x)) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq35434
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq35434
    | exact resolve eq35434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35434
  have eq35460 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq35437
       have i₂ := eq35377
       grind)
    | exact superpose eq35377 eq35437
    | exact resolve eq35437 eq35377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35377 eq35437
  have eq35472 : (σ (k x x)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq32991 eq35457
    | exact resolve eq35457 eq32991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32991 eq35457
  have eq35484 : x = (σ (k x x)) := by
    first
    | exact superpose eq35450 eq35472
    | exact resolve eq35472 eq35450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35450 eq35472
  have eq35493 : x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35484
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq35484
    | exact resolve eq35484 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq35484
  have eq35500 : x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35493
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35493
    | exact resolve eq35493 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35493
  have eq35505 : x = (σ x) := by
    first
    | exact superpose eq35446 eq35500
    | exact resolve eq35500 eq35446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35446 eq35500
  have eq36693 : x = (M.op x y) := by
    first
    | exact superpose eq35460 eq184
    | exact resolve eq184 eq35460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq35460
  have eq36696 : x = (M.op x y) := by
    first
    | (have i₁ := eq36693
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36693
    | exact resolve eq36693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq36693
  have eq36848 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq36696
       grind)
    | exact superpose eq36696 eq22
    | exact resolve eq22 eq36696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq36881 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq35505
       have i₂ := eq36696
       grind)
    | exact superpose eq36696 eq35505
    | exact resolve eq35505 eq36696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35505 eq36696
  have eq36903 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36881 eq36848
    | exact resolve eq36848 eq36881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36848 eq36881
  have eq37307 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36903 eq20
    | exact resolve eq20 eq36903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq36903
  have eq37468 : False := by grind
  exact eq37468

/-- `Equation4399`: `x ◇ (x ◇ y) = (x ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_y_pxy_Equation4399 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4399 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4399.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
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
  have eq52 : (M.op x (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq10
    | exact resolve eq10 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq43
    | exact resolve eq43 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq67 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq63 sF2
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq65
    | exact resolve eq65 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq63 sF2
       grind)
    | exact superpose eq63 eq49
    | exact resolve eq49 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq74
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq74
    | exact resolve eq74 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) := by
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
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq108 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq112 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq63 sF3
       grind)
    | exact superpose eq63 eq108
    | exact resolve eq108 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq114 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq63 y
       grind)
    | exact superpose eq63 eq112
    | exact resolve eq112 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq112
  have eq762 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq763 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq762
    | (have j0 := eq762 X0 X1
       grind)
    | exact resolve eq762 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq762
  have eq812 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq763 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq763
    | (have j0 := eq763 X0 y
       grind)
    | exact resolve eq763 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq838 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq812 X0
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq812
    | (have j0 := eq812 X0
       grind)
    | exact resolve eq812 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq4114 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 y))) = (M.op (σ (k X0 y)) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq838 eq14
    | (have j1 := eq838 X0
       grind)
    | exact resolve eq14 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4122 : ∀ X0 : G, (σ (k X0 y)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq22296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq22296
    | exact resolve eq22296 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22296
  have eq22315 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq22304
       have r₂ := eq27
       grind)
    | exact resolve eq22304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22304
  have eq22319 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq22315
    | exact resolve eq22315 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22315
  have eq22321 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq22319
    | exact resolve eq22319 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22319
  have eq22334 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq22321 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq22321
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22321
       grind)
    | exact resolve eq13 eq22321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22321
  have eq27927 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq22334
    | (have j0 := eq22334 (σ x)
       grind)
    | (have r₁ := eq22334 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq22334 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22334
  have eq27932 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq27927
  have eq27943 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27932 eq59
    | exact resolve eq59 eq27932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27932
  have eq27975 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq75 eq27943
    | exact resolve eq27943 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27943
  have eq28295 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq27975
       grind)
    | exact superpose eq27975 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq27975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27975
  have eq28304 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq28295
  have eq28313 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq28304
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28304
    | exact resolve eq28304 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28304
  have eq28314 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq28313
  have eq28334 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq28314
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28314
    | exact resolve eq28314 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28314
  have eq28335 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq28334
  have eq28412 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq28335 eq78
    | (have r₁ := eq78
       have r₂ := eq28335
       grind)
    | exact resolve eq78 eq28335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28439 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq28412
  have eq29659 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq28439 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq28439
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq28439
       grind)
    | exact resolve eq13 eq28439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28439
  have eq604932 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq29659
    | (have j0 := eq29659 (σ x)
       grind)
    | (have r₁ := eq29659 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq29659 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29659
  have eq604940 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq604932
  have eq604951 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq100 eq604940
    | exact resolve eq604940 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604956 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq604940 eq100
    | exact resolve eq100 eq604940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq604940
  have eq604996 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq604956
  have eq604998 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq604951
  have eq605039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq604998 eq28335
    | exact resolve eq28335 eq604998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604998
  have eq605699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq605039
  have eq605707 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq605699
       have r₂ := eq27
       grind)
    | exact resolve eq605699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605699
  have eq605724 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq605707
       grind)
    | exact superpose eq605707 eq114
    | exact resolve eq114 eq605707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605739 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq605707
       grind)
    | exact superpose eq605707 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq605707
       grind)
    | exact resolve eq13 eq605707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605707
  have eq605792 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq605724
    | exact resolve eq605724 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605724
  have eq669606 : (τ (σ y)) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq604996 eq59
    | exact resolve eq59 eq604996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604996
  have eq669665 : y = (k x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29 eq669606
    | exact resolve eq669606 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669606
  have eq669679 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq669665
       have r₂ := eq77
       grind)
    | exact resolve eq669665 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669665
  have eq669694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq669679 eq28335
    | exact resolve eq28335 eq669679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28335 eq669679
  have eq670356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) := by grind
  clear eq669694
  have eq670676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq670356
       have r₂ := eq77
       grind)
    | exact resolve eq670356 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq670356
  have eq670692 : (M.op x y) = (M.op y y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq670676
       have r₂ := eq27
       grind)
    | exact resolve eq670676 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670676
  have eq670700 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq670692
       grind)
    | exact superpose eq670692 eq114
    | exact resolve eq114 eq670692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670720 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) ∨ y = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq670692
       grind)
    | exact superpose eq670692 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq670692
       grind)
    | exact resolve eq13 eq670692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670692
  have eq670771 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq20 eq670700
    | exact resolve eq670700 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670700
  have eq711901 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq670720 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq670720
    | (have j0 := eq670720 x
       grind)
    | (have r₁ := eq670720 x
       have r₂ := eq18
       grind)
    | exact resolve eq670720 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670720
  have eq711910 : (k x y) = (M.op x x) ∨ y = (k x y) := by grind
  clear eq711901
  have eq711935 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq4122 x
       have i₂ := eq711910
       grind)
    | exact superpose eq711910 eq4122
    | (have j0 := eq4122 x
       grind)
    | exact resolve eq4122 eq711910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4122 eq711910
  have eq711964 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq711935
  have eq711991 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq711964
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq711964
    | exact resolve eq711964 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711964
  have eq712035 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq711991
    | exact resolve eq711991 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711991
  have eq712064 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq712035
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq712035
    | exact resolve eq712035 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712035
  have eq712093 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq712064
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq712064
    | exact resolve eq712064 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712064
  have eq712119 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq712093
    | exact resolve eq712093 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712093
  have eq713363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | exact superpose eq712119 eq670771
    | exact resolve eq670771 eq712119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712119
  have eq713429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq713363
  have eq713447 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have r₁ := eq713429
       have r₂ := eq27
       grind)
    | exact resolve eq713429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713429
  have eq713460 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq713447 eq78
    | (have r₁ := eq78
       have r₂ := eq713447
       grind)
    | exact resolve eq78 eq713447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq713447
  have eq713655 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq713460
  have eq719102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq713655 eq670771
    | exact resolve eq670771 eq713655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670771 eq713655
  have eq719168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq719102
  have eq719191 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have r₁ := eq719168
       have r₂ := eq27
       grind)
    | exact resolve eq719168 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719168
  have eq719211 : (τ (σ y)) = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq719191 eq59
    | exact resolve eq59 eq719191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq719191
  have eq719269 : y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq29 eq719211
    | exact resolve eq719211 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719211
  have eq719270 : y = (k x y) := by grind
  clear eq719269
  have eq719289 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq719270
       grind)
    | exact superpose eq719270 eq44
    | exact resolve eq44 eq719270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq719306 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4114 x
       have i₂ := eq719270
       grind)
    | exact superpose eq719270 eq4114
    | (have j0 := eq4114 x
       grind)
    | exact resolve eq4114 eq719270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114
  have eq719363 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq719306
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq719306
    | exact resolve eq719306 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719306
  have eq719364 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) := by grind
  clear eq719363
  have eq719378 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq719289
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq719289
    | exact resolve eq719289 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719289
  have eq719407 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq719364
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq719364
    | exact resolve eq719364 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719364
  have eq719436 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq719407
    | exact resolve eq719407 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719407
  have eq719462 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq719436
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq719436
    | exact resolve eq719436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq719436
  have eq719485 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq719462
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq719462
    | exact resolve eq719462 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719462
  have eq719506 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq719485
    | exact resolve eq719485 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719485
  have eq729545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq719506 eq605792
    | exact resolve eq605792 eq719506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729594 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq719506 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq719506
       grind)
    | exact resolve eq13 eq719506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729629 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq729545
       have r₂ := eq27
       grind)
    | exact resolve eq729545 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729545
  have eq733940 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq729629 eq75
    | exact resolve eq75 eq729629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729629
  have eq740108 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by grind
  have eq927474 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq729594
    | (have j0 := eq729594 (σ x)
       grind)
    | (have r₁ := eq729594 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq729594 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729594
  have eq927492 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq927474
  have eq927497 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq719378 eq927492
    | exact resolve eq927492 eq719378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719378 eq927492
  have eq932602 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  have eq1664022 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq605739 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq605739
    | (have j0 := eq605739 x
       grind)
    | (have r₁ := eq605739 x
       have r₂ := eq18
       grind)
    | exact resolve eq605739 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605739
  have eq1664037 : (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1664022
  have eq1664044 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1664037
       have i₂ := eq719270
       grind)
    | exact superpose eq719270 eq1664037
    | exact resolve eq1664037 eq719270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664037
  have eq1665114 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1664044
       have i₂ := eq733940
       grind)
    | exact superpose eq733940 eq1664044
    | exact resolve eq1664044 eq733940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733940 eq1664044
  have eq1665254 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1665114
  have eq1665287 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1665254
       have r₂ := eq740108
       grind)
    | exact resolve eq1665254 eq740108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740108 eq1665254
  have eq1665318 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq1665287
       grind)
    | exact superpose eq1665287 eq67
    | exact resolve eq67 eq1665287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1665287
  have eq1665487 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq1665318
    | exact resolve eq1665318 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665318
  have eq1665875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1665487 eq927497
    | exact resolve eq927497 eq1665487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927497 eq1665487
  have eq1666134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1665875
  have eq1666149 : y = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1666134
       have r₂ := eq27
       grind)
    | exact resolve eq1666134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666134
  have eq1666257 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1666149 eq15
    | exact resolve eq15 eq1666149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666149
  have eq1666854 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1666257
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1666257
    | exact resolve eq1666257 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666257
  have eq1666875 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1666854 eq53
    | exact resolve eq53 eq1666854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1667172 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1666854 eq932602
    | (have r₁ := eq932602
       have r₂ := eq1666854
       grind)
    | exact resolve eq932602 eq1666854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932602 eq1666854
  have eq1667232 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1667172
  have eq1667306 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq1666875
    | exact resolve eq1666875 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1666875
  have eq1668432 : (τ (σ y)) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1667232 eq75
    | exact resolve eq75 eq1667232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667232
  have eq1668916 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq1668432
    | exact resolve eq1668432 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668432
  have eq1668954 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1667306 eq605792
    | exact resolve eq605792 eq1667306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605792 eq1667306
  have eq1669101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1668954
  have eq1669123 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1669101
       have r₂ := eq27
       grind)
    | exact resolve eq1669101 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669101
  have eq1670933 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1668916
       have i₂ := eq1669123
       grind)
    | exact superpose eq1669123 eq1668916
    | exact resolve eq1668916 eq1669123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668916 eq1669123
  have eq1670962 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1670933
  have eq1671011 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1670962 eq29
    | exact resolve eq29 eq1670962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1670962
  have eq1671607 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq1671011
    | exact resolve eq1671011 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1671011
  have eq1671608 : y = (M.op x y) := by grind
  clear eq1671607
  have eq1671663 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1671608 eq20
    | exact resolve eq20 eq1671608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1671665 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1671608 eq52
    | exact resolve eq52 eq1671608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1672232 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1671665
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1671665
    | exact resolve eq1671665 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671665
  have eq1672234 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1671663
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1671663
    | exact resolve eq1671663 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671663
  have eq1672288 : y = (M.op y y) := by
    first
    | exact superpose eq1671608 eq1672232
    | exact resolve eq1672232 eq1671608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672232
  have eq1672630 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1672234 eq719506
    | exact resolve eq719506 eq1672234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719506
  have eq1673080 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq1672288
       grind)
    | exact superpose eq1672288 eq114
    | exact resolve eq114 eq1672288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1673273 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1672288
       grind)
    | exact superpose eq1672288 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq1672288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672288
  have eq1673354 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1672234 eq1673080
    | exact resolve eq1673080 eq1672234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673080
  have eq1673395 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1673354
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1673354
    | exact resolve eq1673354 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673354
  have eq1673433 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1672234 eq1673395
    | exact resolve eq1673395 eq1672234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673395
  have eq1720559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1673433 eq1672630
    | exact resolve eq1672630 eq1673433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672630 eq1673433
  have eq1720560 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq1720559
       have r₂ := eq27
       grind)
    | exact resolve eq1720559 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720559
  have eq1720565 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1720560 eq75
    | exact resolve eq75 eq1720560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1720560
  have eq1938599 : y ≠ (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq1673273 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1673273
    | (have j0 := eq1673273 x
       grind)
    | exact resolve eq1673273 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1673273
  have eq1938611 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq1938599
       have r₂ := eq1671608
       grind)
    | exact resolve eq1938599 eq1671608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671608 eq1938599
  have eq1938616 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1938611
       have i₂ := eq1720565
       grind)
    | exact superpose eq1720565 eq1938611
    | exact resolve eq1938611 eq1720565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720565 eq1938611
  have eq1938621 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1938616
       have i₂ := eq719270
       grind)
    | exact superpose eq719270 eq1938616
    | exact resolve eq1938616 eq719270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719270 eq1938616
  have eq1938729 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1938621 eq15
    | exact resolve eq15 eq1938621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938621
  have eq1939619 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1938729
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1938729
    | exact resolve eq1938729 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1938729
  have eq1939789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1672234 eq1939619
    | exact resolve eq1939619 eq1672234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672234 eq1939619
  have eq1939929 : False := by grind
  exact eq1939929
