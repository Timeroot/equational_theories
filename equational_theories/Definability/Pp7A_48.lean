import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pxy_pyx_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq85 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 (M.op x x) x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq472 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq473 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq496 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq472 eq57
    | exact resolve eq57 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq515 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq473 eq57
    | exact resolve eq57 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq473
  have eq30272 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (M.op (σ x) (σ x)) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq30273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq30272
    | exact resolve eq30272 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30272
  have eq30284 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq30273
       have r₂ := eq28
       grind)
    | exact resolve eq30273 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30273
  have eq30981 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq30284 eq69
    | exact resolve eq69 eq30284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30284
  have eq31089 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq30981
    | exact resolve eq30981 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30981
  have eq31090 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq31089
  have eq31112 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq31090
       grind)
    | exact superpose eq31090 eq52
    | exact resolve eq52 eq31090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq31127 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq31090
       grind)
    | exact superpose eq31090 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq31090
       grind)
    | exact resolve eq12 eq31090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31090
  have eq31186 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq31127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31127
  have eq31224 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31112
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31112
    | exact resolve eq31112 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31112
  have eq31259 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq31224 eq12
    | (have j0 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq31224
       grind)
    | exact resolve eq12 eq31224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31224
  have eq31318 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq31259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31259
  have eq53898 : (σ (M.op y x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq85
       have i₂ := eq31186 y
       grind)
    | exact superpose eq31186 eq85
    | (have j1 := eq31186 y
       grind)
    | exact resolve eq85 eq31186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq31186
  have eq53918 : (σ (M.op y x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq53898
  have eq53936 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq53918
       have i₂ := eq496
       grind)
    | exact superpose eq496 eq53918
    | exact resolve eq53918 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq53918
  have eq53965 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq53936
    | exact resolve eq53936 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53936
  have eq63643 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31318 eq53965
    | (have j1 := eq31318 (σ y)
       grind)
    | exact resolve eq53965 eq31318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31318 eq53965
  have eq63648 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq63643
  have eq63673 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq515 eq63648
    | exact resolve eq63648 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515 eq63648
  have eq63710 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq63673
       have r₂ := eq28
       grind)
    | exact resolve eq63673 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63673
  have eq65716 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq63710 eq30
    | exact resolve eq30 eq63710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq63710
  have eq65853 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq65716
    | exact resolve eq65716 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq65716
  have eq65854 : x = y := by grind
  clear eq65853
  have eq65874 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq65854
       grind)
    | exact superpose eq65854 eq19
    | exact resolve eq19 eq65854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq65875 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq65854
       grind)
    | exact superpose eq65854 eq25
    | exact resolve eq25 eq65854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq65854
  have eq66012 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq65875
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65875
    | exact resolve eq65875 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq65875
  have eq66029 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq66012 eq27
    | exact resolve eq27 eq66012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq66012
  have eq68485 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq66029 eq69
    | exact resolve eq69 eq66029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq66029
  have eq68684 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq68485
       have i₂ := eq65874
       grind)
    | exact superpose eq65874 eq68485
    | exact resolve eq68485 eq65874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65874 eq68485
  have eq68724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq68684 eq15
    | exact resolve eq15 eq68684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68684
  have eq68767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq68724
    | exact resolve eq68724 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq68724
  have eq68776 : False := by grind
  exact eq68776

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyx_pxy_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq52
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 (M.op y y) y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
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
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq89 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq93 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq89
  have eq94 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq93
  have eq125 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq16
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq474 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq497 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq473 eq57
    | exact resolve eq57 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq516 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq474 eq57
    | exact resolve eq57 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq474
  have eq30067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (M.op (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq30068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq30067
    | exact resolve eq30067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30067
  have eq30079 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq30068
       have r₂ := eq28
       grind)
    | exact resolve eq30068 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30068
  have eq30083 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30079 eq125
    | exact resolve eq125 eq30079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq30079
  have eq30196 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq30083
    | exact resolve eq30083 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30083
  have eq30197 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30196
  have eq30218 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq30197
       grind)
    | exact superpose eq30197 eq94
    | exact resolve eq94 eq30197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq30238 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq30197
       grind)
    | exact superpose eq30197 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq30197
       grind)
    | exact resolve eq12 eq30197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30197
  have eq30295 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30238
  have eq30334 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq30218
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30218
    | exact resolve eq30218 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30218
  have eq31072 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30334 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq30334
       grind)
    | exact resolve eq12 eq30334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30334
  have eq31131 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq31072 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31072
  have eq57033 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq30295 x
       grind)
    | exact superpose eq30295 eq49
    | (have j1 := eq30295 x
       grind)
    | exact resolve eq49 eq30295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq30295
  have eq57053 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq57033
  have eq57064 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57053
       have i₂ := eq497
       grind)
    | exact superpose eq497 eq57053
    | exact resolve eq57053 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq57053
  have eq57078 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq57064
    | exact resolve eq57064 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57064
  have eq67611 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31131 eq57078
    | (have j1 := eq31131 (σ x)
       grind)
    | exact resolve eq57078 eq31131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31131 eq57078
  have eq67616 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq67611
  have eq67641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq516 eq67616
    | exact resolve eq67616 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq67616
  have eq67666 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq67641
       have r₂ := eq28
       grind)
    | exact resolve eq67641 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67641
  have eq67669 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq67666 eq30
    | exact resolve eq30 eq67666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq67666
  have eq67802 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq67669
    | exact resolve eq67669 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq67669
  have eq67803 : x = y := by grind
  clear eq67802
  have eq67821 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq67803
       grind)
    | exact superpose eq67803 eq19
    | exact resolve eq19 eq67803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq67822 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq67803
       grind)
    | exact superpose eq67803 eq25
    | exact resolve eq25 eq67803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq67803
  have eq67959 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq67822
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq67822
    | exact resolve eq67822 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq67822
  have eq67976 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq67959 eq27
    | exact resolve eq27 eq67959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq67959
  have eq71221 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq67976 eq69
    | exact resolve eq69 eq67976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq67976
  have eq71408 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq71221
       have i₂ := eq67821
       grind)
    | exact superpose eq67821 eq71221
    | exact resolve eq71221 eq67821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67821 eq71221
  have eq71799 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71408 eq15
    | exact resolve eq15 eq71408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71408
  have eq71843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq71799
    | exact resolve eq71799 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq71799
  have eq71852 : False := by grind
  exact eq71852

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) y) X0) = X0 := by
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
  have eq52 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
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
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
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
  have eq97 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq92
    | (have j0 := eq92 (σ x) (σ X0)
       grind)
    | exact resolve eq92 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq44
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq138 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq155 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq127
  have eq579 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq578
  have eq583 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq579 eq52
    | exact resolve eq52 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq593 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq583 eq52
    | exact resolve eq52 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq624 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq118
       have i₂ := eq593 (k sF2 sF3)
       grind)
    | exact superpose eq593 eq118
    | (have j1 := eq593 X0
       grind)
    | exact resolve eq118 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq628 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq624 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq633 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq628 X0
       grind)
    | (have r₁ := eq628 X0
       have r₂ := eq129
       grind)
    | exact resolve eq628 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq628
  have eq701 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq633 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq633 (σ y)
       grind)
    | exact resolve eq13 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq702 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq1168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq702 eq118
    | exact resolve eq118 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq702
  have eq1172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1168
  have eq1178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1172
    | exact resolve eq1172 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1180 : x = (M.op x y) := by
    first
    | (have r₁ := eq1178
       have r₂ := eq27
       grind)
    | exact resolve eq1178 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1183 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1180 eq20
    | exact resolve eq20 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1185 : ∀ X0 : G, (M.op (M.op (M.op y x) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1180 eq50
    | exact resolve eq50 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1187 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq1180 eq74
    | (have r₁ := eq74
       have r₂ := eq1180
       grind)
    | exact resolve eq74 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1191 : y = (M.op y y) ∨ x = (k x y) := by grind
  clear eq1187
  have eq1197 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1183
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1183
    | exact resolve eq1183 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1198 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1197 eq26
    | exact resolve eq26 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1342 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq52 y X0
       have i₂ := eq1191
       grind)
    | exact superpose eq1191 eq52
    | exact resolve eq52 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq2155 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1197 eq97
    | (have j0 := eq97 X0
       grind)
    | exact resolve eq97 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2156 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1197 eq2155
    | (have j0 := eq2155 X0
       grind)
    | exact resolve eq2155 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq2224 : (σ (k x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2156 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2156
    | (have j0 := eq2156 y
       grind)
    | exact resolve eq2156 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2156
  have eq2234 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1198 eq2224
    | exact resolve eq2224 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq2250 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2234
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq2234
    | exact resolve eq2234 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2234
  have eq2261 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1197 eq2250
    | exact resolve eq2250 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250
  have eq2269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1198 eq2261
    | exact resolve eq2261 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq2261
  have eq2272 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq2269
       have r₂ := eq27
       grind)
    | exact resolve eq2269 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2278 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq2272 eq155
    | exact resolve eq155 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq2281 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1180 eq2278
    | exact resolve eq2278 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278
  have eq2456 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1342 X0
       have i₂ := eq2281
       grind)
    | exact superpose eq2281 eq1342
    | (have j0 := eq1342 X0
       grind)
    | exact resolve eq1342 eq2281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342 eq2281
  have eq2461 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq52 y X0
       have i₂ := eq2456 y
       grind)
    | exact superpose eq2456 eq52
    | exact resolve eq52 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2456
  have eq2486 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1185 X0
       have i₂ := eq2461 x
       grind)
    | exact superpose eq2461 eq1185
    | exact resolve eq1185 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185 eq2461
  have eq2514 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2486 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2486
    | (have j0 := eq2486 X0
       grind)
    | exact resolve eq2486 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486
  have eq2516 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1180 eq2514
    | exact resolve eq2514 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514
  have eq2530 : y = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2516 y
       grind)
    | exact superpose eq2516 eq18
    | (have j1 := eq2516 y
       grind)
    | exact resolve eq18 eq2516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2516
  have eq2552 : x = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq1180 eq2530
    | exact resolve eq2530 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530
  have eq2556 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2552 eq15
    | exact resolve eq15 eq2552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq2570 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2556
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2556
    | exact resolve eq2556 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556
  have eq2571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1197 eq2570
    | exact resolve eq2570 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570
  have eq2572 : x = y := by
    first
    | (have r₁ := eq2571
       have r₂ := eq27
       grind)
    | exact resolve eq2571 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq2573 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2572
       grind)
    | exact superpose eq2572 eq18
    | exact resolve eq18 eq2572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2581 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq138
       have i₂ := eq2572
       grind)
    | exact superpose eq2572 eq138
    | exact resolve eq138 eq2572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq2572
  have eq2608 : (M.op (σ x) (σ y)) = (σ (k (M.op x y) x)) := by
    first
    | exact superpose eq2272 eq2581
    | exact resolve eq2581 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272 eq2581
  have eq2615 : x = (M.op x x) := by
    first
    | exact superpose eq1180 eq2573
    | exact resolve eq2573 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq2573
  have eq2616 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq137 eq2608
    | exact resolve eq2608 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq2608
  have eq2622 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1197 eq2616
    | exact resolve eq2616 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2616
  have eq2717 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq2615
       grind)
    | exact superpose eq2615 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq2615
       grind)
    | exact resolve eq13 eq2615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2718 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq2717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717
  have eq3839 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2718 x
       grind)
    | exact superpose eq2718 eq43
    | exact resolve eq43 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2718
  have eq3864 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3839
       have i₂ := eq2615
       grind)
    | exact superpose eq2615 eq3839
    | exact resolve eq3839 eq2615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615 eq3839
  have eq3884 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1197 eq3864
    | exact resolve eq3864 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3864
  have eq3898 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2622 eq3884
    | exact resolve eq3884 eq2622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2622 eq3884
  have eq3910 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3898
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3898
    | exact resolve eq3898 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3898
  have eq3921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1197 eq3910
    | exact resolve eq3910 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq3910
  have eq3930 : False := by grind
  exact eq3930

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
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
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X0) ≠ (M.op (M.op X0 (M.op X1 X0)) X0) ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X0)
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X0) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X1)
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X1) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq51 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op X1 (M.op X2 X1)) X1) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X1) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq51 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq56 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq40
    | exact resolve eq40 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op (M.op X1 (M.op X2 X1)) X1)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (M.op (M.op X1 (M.op X2 X1)) X1) X0
       have i₂ := eq54 (σ X0) X1 X2
       grind)
    | exact superpose eq54 eq30
    | (have j1 := eq54 (σ X0) X1 X2
       grind)
    | exact resolve eq30 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq125 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (M.op (M.op X1 (M.op X2 X1)) X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq121
    | (have j0 := eq121 X0 X1 X2
       grind)
    | exact resolve eq121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq348 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq350 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq344 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq354 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq350 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq350 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq367 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq348 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq348
    | (have j0 := eq348 (τ X0)
       grind)
    | exact resolve eq348 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq371 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq367 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq367
    | (have j0 := eq367 X0
       grind)
    | exact resolve eq367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq378 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq371
    | (have j0 := eq371 X0
       grind)
    | exact resolve eq371 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq388 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq378 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq378
    | (have j0 := eq378 (τ X0)
       grind)
    | exact resolve eq378 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq395 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) ∨ (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq354 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq33 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq33 eq354
    | (have j0 := eq354 (M.op (M.op X0 X0) X0) X1
       grind)
    | exact resolve eq354 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq354 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq354
    | (have j0 := eq354 (τ X0) X1
       grind)
    | exact resolve eq354 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq354
  have eq406 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq402
    | (have j0 := eq402 X0 X1
       grind)
    | exact resolve eq402 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq411 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq395 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq395
    | (have j0 := eq395 X0 X1
       grind)
    | exact resolve eq395 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq412 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq411 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq413 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq406
    | (have j0 := eq406 X0 X1
       grind)
    | exact resolve eq406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq423 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq413 (τ X0) X1
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq413
    | (have j0 := eq413 (τ X0) X1
       grind)
    | exact resolve eq413 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq557 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) ≠ (τ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) ∨ (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq388 (M.op (M.op X0 X0) X0)
       have i₂ := eq33 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq33 eq388
    | (have j0 := eq388 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq388 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 : G, (τ (M.op (M.op X0 (M.op X1 X0)) X0)) ≠ (τ (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op (M.op X0 (M.op X1 X0)) X0))) ∨ (τ (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X0)) (τ (M.op (M.op X0 (M.op X1 X0)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq388 (M.op (M.op X0 (M.op X1 X0)) X0)
       have i₂ := eq34 X0 X1 (M.op (M.op X0 (M.op X1 X0)) X0)
       grind)
    | exact superpose eq34 eq388
    | (have j0 := eq388 (M.op (M.op X0 (M.op X1 X0)) X0)
       grind)
    | exact resolve eq388 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq388
  have eq579 : ∀ X0 X1 : G, (τ (M.op (M.op X0 (M.op X1 X0)) X0)) ≠ (τ (M.op (M.op X0 (M.op X1 X0)) X0)) ∨ (τ (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X0)) (τ (M.op (M.op X0 (M.op X1 X0)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X0) X0 X1
       grind)
    | exact superpose eq9 eq558
    | (have j0 := eq558 X0 X1
       grind)
    | exact resolve eq558 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq580 : ∀ X0 X1 : G, (τ (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X0)) (τ (M.op (M.op X0 (M.op X1 X0)) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq579 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq581 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) ≠ (τ (M.op (M.op X0 X0) X0)) ∨ (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq557 X0
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq557 X0
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq557
    | (have j0 := eq557 X0
       grind)
    | exact resolve eq557 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq582 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have j0 := eq581 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq821 : ∀ X0 X1 : G, (σ (k X0 (M.op (M.op X1 X1) X1))) = (M.op (σ X0) (σ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq412 X1 (σ X0)
       grind)
    | exact superpose eq412 eq15
    | exact resolve eq15 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq844 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op (M.op X1 X1) X1))) = (σ (M.op X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq821 X0 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq821
    | exact resolve eq821 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq821
  have eq1593 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq83 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1594 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq1593 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1596 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1594 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1594
    | (have j0 := eq1594 X0
       grind)
    | exact resolve eq1594 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1631 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1596 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1596
    | exact resolve eq1596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1668 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1631 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1631
    | (have j0 := eq1631 X0
       grind)
    | exact resolve eq1631 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq1688 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq1668 X0
       grind)
    | exact superpose eq1668 eq10
    | (have j1 := eq1668 X0
       grind)
    | exact resolve eq10 eq1668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1731 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1688 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1688
    | (have j0 := eq1688 X0
       grind)
    | exact resolve eq1688 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1738 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1731 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1731 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1731 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq1754 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X1
       have i₂ := eq1738 X0
       grind)
    | exact superpose eq1738 eq423
    | (have j0 := eq423 X0 X1
       grind)
    | exact resolve eq423 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq1770 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1738 (σ X0)
       grind)
    | exact superpose eq1738 eq15
    | exact resolve eq15 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1779 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq1738 (τ X0)
       grind)
    | exact superpose eq1738 eq43
    | exact resolve eq43 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1796 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1779 X0
       have i₂ := eq1738 X0
       grind)
    | exact superpose eq1738 eq1779
    | exact resolve eq1779 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1802 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1770 X0
       have i₂ := eq1738 X0
       grind)
    | exact superpose eq1738 eq1770
    | exact resolve eq1770 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738 eq1770
  have eq1892 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op X0 X0)) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ X0) X1
       have i₂ := eq1796 X0
       grind)
    | exact superpose eq1796 eq19
    | exact resolve eq19 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2048 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X0)) (τ (M.op (M.op X0 (M.op X1 X0)) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1892 (M.op (M.op X0 (M.op X1 X0)) X0) X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X0) X0 X1
       grind)
    | exact superpose eq9 eq1892
    | exact resolve eq1892 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2049 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1892 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq19 eq1892
    | exact resolve eq1892 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1892
  have eq2130 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2049 X0 X1
       have i₂ := eq582 X0
       grind)
    | exact superpose eq582 eq2049
    | exact resolve eq2049 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049
  have eq2131 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2048 X0 X1 X2
       have i₂ := eq580 X0 X1
       grind)
    | exact superpose eq580 eq2048
    | exact resolve eq2048 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2170 : ∀ X0 X1 : G, (M.op (τ (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2130 (τ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq2130 X0 (τ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq2130 eq2130
    | exact resolve eq2130 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq2228 : ∀ X0 X1 : G, (M.op (τ (τ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2170 X0 X1
       have i₂ := eq582 X0
       grind)
    | exact superpose eq582 eq2170
    | exact resolve eq2170 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170
  have eq2784 : ∀ X0 X1 : G, (M.op (τ (τ (M.op (τ (τ (M.op (M.op X0 X0) X0))) (τ (τ (M.op (M.op X0 X0) X0)))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2228 (τ (τ (M.op (M.op X0 X0) X0))) X1
       have i₂ := eq2228 X0 (τ (τ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq2228 eq2228
    | exact resolve eq2228 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2857 : ∀ X0 X1 : G, (M.op (τ (τ (τ (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0)))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2784 X0 X1
       have i₂ := eq1796 (τ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq1796 eq2784
    | exact resolve eq2784 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq2890 : ∀ X0 X1 : G, (M.op (τ (τ (τ (τ (M.op (M.op X0 X0) X0))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2857 X0 X1
       have i₂ := eq582 X0
       grind)
    | exact superpose eq582 eq2857
    | exact resolve eq2857 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq2857
  have eq3230 : ∀ X0 X1 X2 : G, (M.op (τ (τ (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X0)) (τ (M.op (M.op X0 (M.op X1 X0)) X0))))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2228 (τ (M.op (M.op X0 (M.op X1 X0)) X0)) X2
       have i₂ := eq2131 X0 X1 (τ (M.op (M.op X0 (M.op X1 X0)) X0))
       grind)
    | exact superpose eq2131 eq2228
    | exact resolve eq2228 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq3237 : ∀ X0 X1 X2 : G, (M.op (τ (τ (τ (M.op (M.op X0 (M.op X1 X0)) X0)))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3230 X0 X1 X2
       have i₂ := eq580 X0 X1
       grind)
    | exact superpose eq580 eq3230
    | exact resolve eq3230 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230
  have eq11731 : ∀ X0 X1 X2 : G, (M.op (τ (τ (τ (τ (M.op (τ (τ (τ (M.op (M.op X0 (M.op X1 X0)) X0)))) (τ (τ (τ (M.op (M.op X0 (M.op X1 X0)) X0))))))))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2890 (τ (τ (τ (M.op (M.op X0 (M.op X1 X0)) X0)))) X2
       have i₂ := eq3237 X0 X1 (τ (τ (τ (M.op (M.op X0 (M.op X1 X0)) X0))))
       grind)
    | exact superpose eq3237 eq2890
    | exact resolve eq2890 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890 eq3237
  have eq11748 : ∀ X0 X1 X2 : G, (M.op (τ (τ (τ (τ (τ (M.op (τ (τ (M.op (M.op X0 (M.op X1 X0)) X0))) (τ (τ (M.op (M.op X0 (M.op X1 X0)) X0))))))))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11731 X0 X1 X2
       have i₂ := eq1796 (τ (τ (M.op (M.op X0 (M.op X1 X0)) X0)))
       grind)
    | exact superpose eq1796 eq11731
    | exact resolve eq11731 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11731
  have eq11808 : ∀ X0 X1 X2 : G, (M.op (τ (τ (τ (τ (τ (τ (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X0)) (τ (M.op (M.op X0 (M.op X1 X0)) X0))))))))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11748 X0 X1 X2
       have i₂ := eq1796 (τ (M.op (M.op X0 (M.op X1 X0)) X0))
       grind)
    | exact superpose eq1796 eq11748
    | exact resolve eq11748 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796 eq11748
  have eq11846 : ∀ X0 X1 X2 : G, (M.op (τ (τ (τ (τ (τ (τ (τ (M.op (M.op X0 (M.op X1 X0)) X0)))))))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11808 X0 X1 X2
       have i₂ := eq580 X0 X1
       grind)
    | exact superpose eq580 eq11808
    | exact resolve eq11808 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq11808
  have eq32067 : ∀ X0 X1 X2 X3 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (k (τ (M.op (M.op X2 (M.op X3 X2)) X2)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1754 (σ X0) X1
       have i₂ := eq125 X0 X2 X3
       grind)
    | exact superpose eq125 eq1754
    | (have j0 := eq1754 (σ X0) X1
       have j1 := eq125 X0 X2 X3
       grind)
    | exact resolve eq1754 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq1754
  have eq32180 : ∀ X0 X1 X2 X3 : G, (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (k (τ (M.op (M.op X2 (M.op X3 X2)) X2)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq32067 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32067
  have eq32234 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (k (τ (M.op (M.op X2 (M.op X3 X2)) X2)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32180 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32180
    | (have j0 := eq32180 X0 X1 X2 X3
       grind)
    | exact resolve eq32180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32180
  have eq313247 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X0)) X2) ≠ X2 ∨ (k (τ (M.op (M.op X0 (M.op X1 X0)) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq32234 X2 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32234
  have eq313249 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op X0 (M.op X1 X0)) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq313247 X0 X1 X2
       grind)
    | (have r₁ := eq313247 X0 X1 X2
       have r₂ := eq2131 X0 X1 X2
       grind)
    | exact resolve eq313247 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131 eq313247
  have eq314972 : ∀ X0 X3 : G, (k (τ (M.op (M.op X0 X0) X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq313249 X0 (τ (τ (τ (τ (τ (τ (τ (M.op (M.op x (M.op x x)) x)))))))) X3
       have i₂ := eq11846 x x X0
       grind)
    | exact superpose eq11846 eq313249
    | exact resolve eq313249 eq11846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11846 eq313249
  have eq315862 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op (M.op X1 X1) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (τ (M.op (M.op X1 X1) X1)) X0
       have i₂ := eq314972 X1 (σ X0)
       grind)
    | exact superpose eq314972 eq30
    | exact resolve eq30 eq314972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq315864 : ∀ X0 X1 X2 : G, (τ (k (σ X0) X2)) = (k (k (τ (τ (M.op (M.op X1 X1) X1))) X0) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (τ (M.op (M.op X1 X1) X1)) X0 X2
       have i₂ := eq314972 X1 (σ X0)
       grind)
    | exact superpose eq314972 eq56
    | exact resolve eq56 eq314972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq314972
  have eq315954 : ∀ X0 X1 X2 : G, (k X0 (τ X2)) = (k (k (τ (τ (M.op (M.op X1 X1) X1))) X0) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq315864 X0 X1 X2
       have i₂ := eq40 X0 X2
       grind)
    | exact superpose eq40 eq315864
    | exact resolve eq315864 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq315864
  have eq315956 : ∀ X0 X1 : G, (k (τ (τ (M.op (M.op X1 X1) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq315862 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq315862
    | exact resolve eq315862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315862
  have eq463832 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = (M.op (k (τ (τ (M.op (M.op X2 X2) X2))) X0) (τ X1)) ∨ (τ X1) = (M.op (k (τ (τ (M.op (M.op X2 X2) X2))) X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (k (τ (τ (M.op (M.op X2 X2) X2))) X0) (τ X1)
       have i₂ := eq315954 X0 X2 X1
       grind)
    | exact superpose eq315954 eq14
    | (have j0 := eq14 (k (τ (τ (M.op (M.op X2 X2) X2))) X0) (τ X1)
       grind)
    | exact resolve eq14 eq315954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315954
  have eq463871 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op (k (τ (τ (M.op (M.op X2 X2) X2))) X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq463832 X0 X1 X2
       have i₂ := eq315956 X0 X2
       grind)
    | exact superpose eq315956 eq463832
    | (have j0 := eq463832 X0 X1 X2
       grind)
    | exact resolve eq463832 eq315956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463832
  have eq464109 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op (k (τ (τ (M.op (M.op X2 X2) X2))) X0) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq463871 X0 X1 X2
       have j1 := eq12 X0 (τ X1)
       grind)
    | (have r₁ := eq463871 X0 X1 X2
       have r₂ := eq12 X0 (τ X1)
       grind)
    | exact resolve eq463871 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463871
  have eq464292 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq464109 X0 X1 x
       have i₂ := eq315956 X0 x
       grind)
    | exact superpose eq315956 eq464109
    | (have j0 := eq464109 X0 X1 x
       grind)
    | exact resolve eq464109 eq315956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315956 eq464109
  have eq465931 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq464292 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq464292
    | exact resolve eq464292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466345 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1 X0
       have i₂ := eq464292 (τ X0) X1
       grind)
    | exact superpose eq464292 eq43
    | (have j1 := eq464292 (τ X0) X1
       grind)
    | exact resolve eq43 eq464292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq464292
  have eq467373 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq465931 (σ X1) (σ X0)
       grind)
    | exact superpose eq465931 eq15
    | (have j1 := eq465931 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq465931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467441 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq465931 X1 (τ X0)
       grind)
    | exact superpose eq465931 eq17
    | (have j1 := eq465931 X1 (τ X0)
       grind)
    | exact resolve eq17 eq465931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq465931
  have eq472053 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq467441 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq467441
    | exact resolve eq467441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467441
  have eq472674 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq472053 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq472053
    | (have j0 := eq472053 X0 X1
       grind)
    | exact resolve eq472053 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472053
  have eq599446 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq466345 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466345
  have eq600498 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq599446 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq599446
    | (have j0 := eq599446 (σ X0) (σ X1)
       grind)
    | exact resolve eq599446 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599446
  have eq601090 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq600498 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq600498
    | (have j0 := eq600498 X0 X1
       grind)
    | exact resolve eq600498 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600498
  have eq601139 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq601090 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq601090
    | (have j0 := eq601090 X0 X1
       grind)
    | exact resolve eq601090 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601090
  have eq601169 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq601139 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq601139
    | (have j0 := eq601139 X0 X1
       grind)
    | exact resolve eq601139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601139
  have eq601189 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq601169 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq601169
    | (have j0 := eq601169 X0 X1
       grind)
    | exact resolve eq601169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601169
  have eq602307 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq601189 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq601189
    | (have j0 := eq601189 (σ X0) (σ X1)
       grind)
    | exact resolve eq601189 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601189
  have eq610783 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq467373 x y
       grind)
    | exact superpose eq467373 eq16
    | (have j1 := eq467373 x y
       grind)
    | exact resolve eq16 eq467373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467373
  have eq612803 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq610783
       have i₂ := eq472674 x y
       grind)
    | exact superpose eq472674 eq610783
    | (have j1 := eq472674 (σ x) (σ y)
       grind)
    | (have r₁ := eq610783
       have r₂ := eq472674 x y
       grind)
    | exact resolve eq610783 eq472674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610783
  have eq612808 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq612803
  have eq612817 : y ≠ y ∨ y = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq612808
       grind)
    | exact superpose eq612808 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq612808
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq612808
       grind)
    | exact resolve eq13 eq612808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612808
  have eq612894 : y = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq612817
  have eq632638 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq602307 x y
       have i₂ := eq612894
       grind)
    | exact superpose eq612894 eq602307
    | (have j0 := eq602307 x y
       grind)
    | exact resolve eq602307 eq612894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602307 eq612894
  have eq632641 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq632638
  have eq632642 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq632641
  have eq632672 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq632642
       grind)
    | exact superpose eq632642 eq16
    | exact resolve eq16 eq632642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632675 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq632642
       grind)
    | exact superpose eq632642 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq632642
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq632642
       grind)
    | exact resolve eq13 eq632642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632642
  have eq632756 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq632675
  have eq632757 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq632756
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq632756
    | exact resolve eq632756 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632756
  have eq632761 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq632757
       have i₂ := eq1802 y
       grind)
    | exact superpose eq1802 eq632757
    | exact resolve eq632757 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802 eq632757
  have eq2259301 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq472674 x y
       have i₂ := eq632761
       grind)
    | exact superpose eq632761 eq472674
    | (have j0 := eq472674 x y
       grind)
    | exact resolve eq472674 eq632761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472674 eq632761
  have eq2259974 : y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2259301
       have r₂ := eq632672
       grind)
    | exact resolve eq2259301 eq632672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259301
  have eq2264112 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq632672
       have i₂ := eq2259974
       grind)
    | exact superpose eq2259974 eq632672
    | exact resolve eq632672 eq2259974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632672 eq2259974
  have eq2264282 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq2264112
  have eq2264283 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq2264282
  have eq2264474 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2264283
       grind)
    | exact superpose eq2264283 eq10
    | exact resolve eq10 eq2264283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264283
  have eq2265129 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2264474
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2264474
    | exact resolve eq2264474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264474
  have eq2265130 : y = (M.op y y) := by grind
  clear eq2265129
  have eq2269517 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (σ (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq844 X0 y
       have i₂ := eq2265130
       grind)
    | exact superpose eq2265130 eq844
    | exact resolve eq844 eq2265130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq2271026 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq2269517 X0
       have i₂ := eq2265130
       grind)
    | exact superpose eq2265130 eq2269517
    | exact resolve eq2269517 eq2265130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265130 eq2269517
  have eq2454876 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2271026 x
       grind)
    | exact superpose eq2271026 eq16
    | (have r₁ := eq16
       have r₂ := eq2271026 x
       grind)
    | exact resolve eq16 eq2271026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271026
  have eq2456018 : False := by grind
  exact eq2456018

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_y_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq47 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k y x) := by
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
  have eq65 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq86 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq208 : (M.op (M.op y (M.op x y)) x) = (k (M.op (M.op y (M.op x y)) x) (M.op (M.op y (M.op x y)) x)) := by grind
  clear eq47
  have eq642 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq50 (M.op X0 X0) x x X3
       have i₂ := eq49 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq49 eq50
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq50
  have eq860 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq8043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8043
    | exact resolve eq8043 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8043
  have eq8055 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8044
       have r₂ := eq28
       grind)
    | exact resolve eq8044 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8044
  have eq8057 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8055
    | exact resolve eq8055 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8055
  have eq8062 : ∀ X0 : G, x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq8057 eq642
    | exact resolve eq642 eq8057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8064 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq8057
  have eq8116 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq642 y X0
       have i₂ := eq8062 X1
       grind)
    | exact superpose eq8062 eq642
    | (have j1 := eq8062 X1
       grind)
    | exact resolve eq642 eq8062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8062
  have eq8134 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8064 eq99
    | exact resolve eq99 eq8064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8064
  have eq8142 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8134
  have eq8156 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq642 y X0
       have i₂ := eq8142
       grind)
    | exact superpose eq8142 eq642
    | exact resolve eq642 eq8142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8142
  have eq8787 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8156 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8156
    | (have j0 := eq8156 y
       grind)
    | exact resolve eq8156 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8156
  have eq10414 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq8116
    | (have j0 := eq8116 X0 (σ y)
       grind)
    | exact resolve eq8116 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8116
  have eq10484 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10414 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10414
    | (have j0 := eq10414 y
       grind)
    | exact resolve eq10414 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10414
  have eq11595 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10484 eq28
    | exact resolve eq28 eq10484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10484
  have eq11613 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11595
       have r₂ := eq8787
       grind)
    | exact resolve eq11595 eq8787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8787 eq11595
  have eq11618 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11613 eq28
    | exact resolve eq28 eq11613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11620 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11613 eq65
    | (have r₁ := eq65
       have r₂ := eq11613
       grind)
    | exact resolve eq65 eq11613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq11613
  have eq11626 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11620
  have eq22579 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11626 eq99
    | exact resolve eq99 eq11626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11626
  have eq22598 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22579
  have eq22610 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22598
       have r₂ := eq11618
       grind)
    | exact resolve eq22598 eq11618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11618 eq22598
  have eq24103 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq22610
  have eq24922 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24103 eq99
    | exact resolve eq99 eq24103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq24103
  have eq24937 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq24922
  have eq24959 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq642 y X0
       have i₂ := eq24937
       grind)
    | exact superpose eq24937 eq642
    | exact resolve eq642 eq24937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24937
  have eq25186 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq24959 y
       grind)
    | exact superpose eq24959 eq19
    | (have j1 := eq24959 y
       grind)
    | exact resolve eq19 eq24959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24959
  have eq25265 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq25186
  have eq25480 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25265 eq30
    | exact resolve eq30 eq25265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25265
  have eq25638 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq25480
    | exact resolve eq25480 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25480
  have eq25639 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq25638
  have eq25640 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25639 eq21
    | exact resolve eq21 eq25639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25688 : (M.op (M.op y y) x) = (k (M.op (M.op y y) x) (M.op (M.op y y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25639 eq208
    | exact resolve eq208 eq25639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25639
  have eq25730 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25688
       have i₂ := eq642 y x
       grind)
    | (have i₁ := eq25688
       have i₂ := eq642 x (M.op (M.op y y) x)
       grind)
    | exact superpose eq642 eq25688
    | exact resolve eq25688 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25688
  have eq25777 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25640
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25640
    | exact resolve eq25640 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25640
  have eq25927 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25777 eq27
    | exact resolve eq27 eq25777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25777
  have eq26271 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq860 x x
       have i₂ := eq25730
       grind)
    | exact superpose eq25730 eq860
    | (have j0 := eq860 x x
       grind)
    | exact resolve eq860 eq25730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25730
  have eq26274 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq26271
  have eq26275 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq26274
  have eq26287 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26275
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26275
    | exact resolve eq26275 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26275
  have eq26788 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26287 eq642
    | exact resolve eq642 eq26287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26287
  have eq27059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26788 eq25927
    | exact resolve eq25927 eq26788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25927 eq26788
  have eq27135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27059
  have eq27182 : x = (M.op x y) := by
    first
    | (have r₁ := eq27135
       have r₂ := eq28
       grind)
    | exact resolve eq27135 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27135
  have eq27203 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq27182 eq21
    | exact resolve eq21 eq27182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq27207 : x ≠ x ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | exact superpose eq27182 eq64
    | (have r₁ := eq64
       have r₂ := eq27182
       grind)
    | exact resolve eq64 eq27182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq27274 : x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq27207
  have eq27335 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq27203
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27203
    | exact resolve eq27203 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27203
  have eq27336 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq27335 eq27
    | exact resolve eq27 eq27335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27791 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq27274
       grind)
    | exact superpose eq27274 eq86
    | exact resolve eq86 eq27274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq27807 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq860 x y
       have i₂ := eq27274
       grind)
    | exact superpose eq27274 eq860
    | (have j0 := eq860 x y
       grind)
    | exact resolve eq860 eq27274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27274
  have eq27810 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq27807
  have eq27815 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27810
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27810
    | exact resolve eq27810 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27810
  have eq27828 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27335 eq27791
    | exact resolve eq27791 eq27335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27791
  have eq27830 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27815
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27815
    | exact resolve eq27815 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27815
  have eq27843 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27828
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27828
    | exact resolve eq27828 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27828
  have eq27844 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq27830
    | exact resolve eq27830 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq27830
  have eq27856 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27335 eq27843
    | exact resolve eq27843 eq27335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27843
  have eq27857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27335 eq27844
    | exact resolve eq27844 eq27335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27844
  have eq27862 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq27857
       have r₂ := eq28
       grind)
    | exact resolve eq27857 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27857
  have eq27867 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27862
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27862
    | exact resolve eq27862 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27862
  have eq27872 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27867
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27867
    | exact resolve eq27867 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27867
  have eq27877 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27335 eq27872
    | exact resolve eq27872 eq27335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27872
  have eq27964 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq27877
  have eq28005 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27964 eq27856
    | exact resolve eq27856 eq27964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27856 eq27964
  have eq28012 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq28005
  have eq28043 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq642 y X0
       have i₂ := eq28012
       grind)
    | exact superpose eq28012 eq642
    | exact resolve eq642 eq28012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28012
  have eq28167 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq28043 y
       grind)
    | exact superpose eq28043 eq19
    | (have j1 := eq28043 y
       grind)
    | exact resolve eq19 eq28043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28043
  have eq28272 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27182 eq28167
    | exact resolve eq28167 eq27182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28167
  have eq28294 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq28272 eq30
    | exact resolve eq30 eq28272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28272
  have eq28451 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq28294
    | exact resolve eq28294 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq28294
  have eq28511 : x = y ∨ x = y := by
    first
    | exact superpose eq27182 eq28451
    | exact resolve eq28451 eq27182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28451
  have eq28512 : x = y := by grind
  clear eq28511
  have eq28518 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq28512
       grind)
    | exact superpose eq28512 eq25
    | exact resolve eq25 eq28512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq28565 : (M.op (M.op x (M.op x y)) x) = (k (M.op (M.op x (M.op x y)) x) (M.op (M.op x (M.op x y)) x)) := by
    first
    | (have i₁ := eq208
       have i₂ := eq28512
       grind)
    | exact superpose eq28512 eq208
    | exact resolve eq208 eq28512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq28512
  have eq28630 : (M.op (M.op x x) x) = (k (M.op (M.op x x) x) (M.op (M.op x x) x)) := by
    first
    | exact superpose eq27182 eq28565
    | exact resolve eq28565 eq27182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27182 eq28565
  have eq28676 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28518
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28518
    | exact resolve eq28518 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28518
  have eq28699 : x = (k x x) := by
    first
    | (have i₁ := eq28630
       have i₂ := eq642 x x
       grind)
    | (have i₁ := eq28630
       have i₂ := eq642 x (M.op (M.op x x) x)
       grind)
    | exact superpose eq642 eq28630
    | exact resolve eq28630 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq28630
  have eq28745 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27335 eq28676
    | exact resolve eq28676 eq27335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28676
  have eq28870 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28745 eq27336
    | exact resolve eq27336 eq28745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27336 eq28745
  have eq29211 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq860 x x
       have i₂ := eq28699
       grind)
    | exact superpose eq28699 eq860
    | (have j0 := eq860 x x
       grind)
    | exact resolve eq860 eq28699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq28699
  have eq29214 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29211
  have eq29215 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29214
  have eq29225 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq29215
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29215
    | exact resolve eq29215 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29215
  have eq29242 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27335 eq29225
    | exact resolve eq29225 eq27335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27335 eq29225
  have eq30868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28870 eq29242
    | exact resolve eq29242 eq28870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28870 eq29242
  have eq30869 : False := by grind
  exact eq30869

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyx_pyx_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq24 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq41 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq48
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq102 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq106 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq59 X1 X0
       grind)
    | (have r₁ := eq102 X1 X0
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq102 X0 X0
       have r₂ := eq59 X0 X0
       grind)
    | exact resolve eq102 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq102
  have eq408 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq106 (σ X1) (σ X0)
       grind)
    | exact superpose eq106 eq15
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 X1
       have i₂ := eq106 X1 X0
       grind)
    | exact superpose eq106 eq408
    | exact resolve eq408 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq408
  have eq419 : False := by grind
  exact eq419

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pyx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq22
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq56 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X1) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq56 X2 X0
       grind)
    | exact superpose eq56 eq9
    | (have j1 := eq56 X2 X0
       grind)
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq56 X2 X0
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq56 X2 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq70 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq71 (σ X0) (σ X1)
       grind)
    | exact superpose eq71 eq15
    | (have j1 := eq71 (σ X0) X1
       grind)
    | exact resolve eq15 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq71 (τ X0) X1
       grind)
    | exact superpose eq71 eq18
    | (have j1 := eq71 (τ X0) X1
       grind)
    | exact resolve eq18 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq71
  have eq82 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq78
  have eq84 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq155 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq24 (M.op X0 X0) x x X3
       have i₂ := eq23 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq24
  have eq196 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq155 X0 X0
       grind)
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq155 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq155 eq68
    | (have j0 := eq68 X0 X1 X2
       grind)
    | exact resolve eq68 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq197 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq196 (σ X1) X2 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq196
    | (have j0 := eq196 (σ X1) X2 X2
       grind)
    | exact resolve eq196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X0)
       have i₂ := eq82 (σ X0) X1
       grind)
    | exact superpose eq82 eq30
    | (have j1 := eq82 (σ X0) X1
       grind)
    | exact resolve eq30 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq82
  have eq507 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq494 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq494
    | (have j0 := eq494 X0 X1
       grind)
    | exact resolve eq494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq512 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq507 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq507
    | (have j0 := eq507 X0 X1
       grind)
    | exact resolve eq507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq517 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq512
    | (have j0 := eq512 X0 X1
       grind)
    | exact resolve eq512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq957 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq197 y x X0
       grind)
    | exact superpose eq197 eq16
    | (have j1 := eq197 X0 x X0
       grind)
    | exact resolve eq16 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq1055 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq10
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq10 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1082 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1055 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1055
    | (have j0 := eq1055 X0 X1
       grind)
    | exact resolve eq1055 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1870 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1082 x y
       grind)
    | exact superpose eq1082 eq16
    | (have j1 := eq1082 x x
       grind)
    | exact resolve eq16 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1896 : x = (k x x) := by
    first
    | (have j1 := eq517 x x
       grind)
    | (have r₁ := eq1870
       have r₂ := eq517 x y
       grind)
    | exact resolve eq1870 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq1870
  have eq1903 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1896
       have i₂ := eq196 x X0 x
       grind)
    | exact superpose eq196 eq1896
    | (have j1 := eq196 x x x
       grind)
    | exact resolve eq1896 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1905 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 x) = X0 ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq70 x X0 x
       have i₂ := eq1896
       grind)
    | exact superpose eq1896 eq70
    | (have j0 := eq70 x X0 x
       grind)
    | exact resolve eq70 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1896
  have eq1911 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq1905 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq1905 X0
       have r₂ := eq13 X0 x
       grind)
    | (have r₁ := eq1905 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1905 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq1930 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq1903 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq1931 : x = (M.op x x) := by grind
  clear eq1930
  have eq1951 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq155 x X0
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq155
    | exact resolve eq155 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq1931
  have eq2751 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq957 X0
       have i₂ := eq1911 y
       grind)
    | exact superpose eq1911 eq957
    | (have j0 := eq957 X0
       have j1 := eq1911 y
       grind)
    | exact resolve eq957 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq2752 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2751 X0
       have i₂ := eq1951 y
       grind)
    | exact superpose eq1951 eq2751
    | (have j0 := eq2751 X0
       grind)
    | exact resolve eq2751 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751
  have eq2753 : ∀ X0 : G, y = (M.op y x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2752 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752
  have eq4074 : ∀ X0 : G, y ≠ y ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2753 X0
       grind)
    | exact superpose eq2753 eq12
    | (have j0 := eq12 y x
       have j1 := eq2753 X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2753 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq2753 (σ x)
       grind)
    | exact resolve eq12 eq2753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2753
  have eq4088 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4074 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4074
  have eq4102 : ∀ X0 : G, y = (k y x) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4088 X0
       have i₂ := eq1951 y
       grind)
    | exact superpose eq1951 eq4088
    | (have j0 := eq4088 X0
       grind)
    | exact resolve eq4088 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4088
  have eq4118 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) X0) = X0 ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq957 X0
       have i₂ := eq4102 X1
       grind)
    | exact superpose eq4102 eq957
    | (have j0 := eq957 X0
       have j1 := eq4102 X0
       grind)
    | exact resolve eq957 eq4102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq4102
  have eq4127 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) X0) = X0 ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4118 X0 X1
       have i₂ := eq1951 y
       grind)
    | exact superpose eq1951 eq4118
    | (have j0 := eq4118 X0 X0
       grind)
    | exact resolve eq4118 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4118
  have eq4128 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4127 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127
  have eq4418 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4128 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4128
  have eq4419 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4418
  have eq4654 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4419 (σ y)
       grind)
    | exact superpose eq4419 eq16
    | exact resolve eq16 eq4419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419
  have eq4756 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4654
       have i₂ := eq1951 y
       grind)
    | exact superpose eq1951 eq4654
    | exact resolve eq4654 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951 eq4654
  have eq4757 : False := by grind
  exact eq4757

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pyx_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq76 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq44
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq82 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq79
    | exact resolve eq79 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq79
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X0 X1) X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X1)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq92 y x
       grind)
    | exact superpose eq92 eq73
    | (have j1 := eq92 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq73 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq120
    | exact resolve eq120 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq121 eq92
    | (have j0 := eq92 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq92 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq121
  have eq186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq185
    | exact resolve eq185 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq189 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq186
       have r₂ := eq28
       grind)
    | exact resolve eq186 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq192 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq189 eq30
    | exact resolve eq30 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq189
  have eq205 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq192
    | exact resolve eq192 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq192
  have eq206 : x = y := by grind
  clear eq205
  have eq209 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq206
       grind)
    | exact superpose eq206 eq19
    | exact resolve eq19 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq210 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq206
       grind)
    | exact superpose eq206 eq25
    | exact resolve eq25 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq206
  have eq221 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq210
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq210
    | exact resolve eq210 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq210
  have eq225 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq221 eq27
    | exact resolve eq27 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq221
  have eq239 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq209
       grind)
    | exact superpose eq209 eq82
    | exact resolve eq82 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq209
  have eq243 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq239
    | exact resolve eq239 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq239
  have eq248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq225 eq243
    | exact resolve eq243 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq243
  have eq249 : False := by grind
  exact eq249
