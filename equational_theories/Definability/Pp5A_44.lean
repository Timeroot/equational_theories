import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxy_pxx_pxy_Equation58 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X2 X0)) X3 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) X0 x
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq42 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq43 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq44 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq65 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq71
    | exact resolve eq71 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42
    | (have j0 := eq42 x
       grind)
    | exact resolve eq42 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42
    | (have j0 := eq42 y
       grind)
    | exact resolve eq42 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq75
    | exact resolve eq75 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq78
    | exact resolve eq78 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq84
    | (have j0 := eq84 (σ X0) (σ X1)
       grind)
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq42 eq84
    | (have j0 := eq84 (σ x) (σ X0)
       grind)
    | exact resolve eq84 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq76
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq76 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq111
    | exact resolve eq111 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq112
       have r₂ := eq27
       grind)
    | exact resolve eq112 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq117 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq115
    | exact resolve eq115 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op X2 X0))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 X0))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) X0
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq12 (M.op X1 X0) X0
       have r₂ := eq37 X0 X1
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq122 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ (M.op y y) = (k y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq34 eq12
    | (have j0 := eq12 y (M.op X0 (M.op x y))
       grind)
    | (have r₁ := eq12 y (M.op X0 (M.op x y))
       have r₂ := eq34 X0
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (M.op y y) = (k y (M.op X0 (M.op x y))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq131 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq132 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq119 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq134 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq117 eq35
    | exact resolve eq35 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq135 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117 eq27
    | exact resolve eq27 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43
    | (have j0 := eq43 y
       grind)
    | exact resolve eq43 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq146 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq142
       have i₂ := eq69 sF3
       grind)
    | exact superpose eq69 eq142
    | exact resolve eq142 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq147 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq146
       have i₂ := eq69 y
       grind)
    | exact superpose eq69 eq146
    | exact resolve eq146 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq153 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq134 eq14
    | exact resolve eq14 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq153
    | (have j0 := eq153 X0 (σ x)
       grind)
    | exact resolve eq153 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq158 eq14
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 y
       grind)
    | exact resolve eq44 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq44
    | (have j0 := eq44 (M.op x y)
       grind)
    | exact resolve eq44 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq84 sF1 (σ X0)
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq183 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq180
       have i₂ := eq69 sF1
       grind)
    | exact superpose eq69 eq180
    | exact resolve eq180 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq183
       have i₂ := eq69 sF0
       grind)
    | exact superpose eq69 eq183
    | exact resolve eq183 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq193 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op X2 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq171 eq14
    | exact resolve eq14 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : (σ (k (M.op x x) y)) = (k (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq47 (M.op x x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq47
    | exact resolve eq47 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq84 (σ X0) sF3
       grind)
    | exact superpose eq84 eq47
    | (have j1 := eq84 (σ X0) (σ y)
       grind)
    | exact resolve eq47 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq247 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op (M.op X2 (M.op (σ x) (σ y))) (M.op X3 (M.op X0 (M.op X1 (σ x))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq193 eq14
    | exact resolve eq14 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq258 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq247 x x x sF2
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq247
    | exact resolve eq247 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq297 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq258 eq14
    | exact resolve eq14 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq346 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq41 X0 (τ X0)
       have i₂ := eq69 (τ X0)
       grind)
    | exact superpose eq69 eq41
    | exact resolve eq41 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq346 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq346
    | exact resolve eq346 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq358 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq357
    | exact resolve eq357 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq357
  have eq564 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X4 (M.op X2 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36 (M.op X1 (M.op X2 X0)) X1 X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq36
    | exact resolve eq36 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X5 (M.op X4 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq36 (M.op X3 X0) X1 (M.op X1 (M.op X2 X0)) X3
       have i₂ := eq36 X0 X1 X2 X3
       grind)
    | exact superpose eq36 eq36
    | exact resolve eq36 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op X0 (M.op X1 (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq36
    | (have j0 := eq36 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq36 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117 eq124
    | (have r₁ := eq124
       have r₂ := eq117
       grind)
    | exact resolve eq124 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq659 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq658
  have eq662 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq659 eq105
    | exact resolve eq105 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq665 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq662
  have eq672 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq665 eq67
    | exact resolve eq67 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq665
  have eq721 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq672
       have r₂ := eq117
       grind)
    | exact resolve eq672 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq763 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq34 eq132
    | (have j0 := eq132 (M.op x y) x x
       grind)
    | exact resolve eq132 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op X1 (M.op X2 (τ X0))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X0 (M.op X1 (M.op X2 (τ X0)))
       have i₂ := eq132 (τ X0) X1 X2
       grind)
    | exact superpose eq132 eq41
    | (have j1 := eq132 (τ X0) X1 X2
       grind)
    | exact resolve eq41 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq858 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq721 eq105
    | exact resolve eq105 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq721
  have eq861 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq858
  have eq865 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq861
       have r₂ := eq27
       grind)
    | exact resolve eq861 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq891 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (σ X1))) = (M.op (M.op X2 (M.op X3 (σ X1))) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36 (σ X1) X2 X3 (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq36
    | (have j1 := eq94 X0 X1
       grind)
    | exact resolve eq36 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq904 : (τ (σ (M.op x y))) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq865 eq92
    | exact resolve eq92 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq907 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq865 eq134
    | exact resolve eq134 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq908 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq865 eq153
    | exact resolve eq153 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq910 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq865 eq158
    | exact resolve eq158 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq926 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op X0 (M.op X1 (σ x))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq865 eq36
    | exact resolve eq36 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq910
  have eq942 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq908 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq943 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq907
  have eq949 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq904
    | exact resolve eq904 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq1005 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq940 eq36
    | exact resolve eq36 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq1026 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ (M.op x y)))) = (M.op (M.op X0 (M.op X1 (σ (M.op x y)))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq943 eq36
    | exact resolve eq36 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq943
  have eq1030 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq949
       grind)
    | exact superpose eq949 eq65
    | (have r₁ := eq65
       have r₂ := eq949
       grind)
    | exact resolve eq65 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 x
       have i₂ := eq949
       grind)
    | exact superpose eq949 eq14
    | exact resolve eq14 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1030
  have eq1156 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1179 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1398 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq14
    | exact resolve eq14 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1634 : (k (σ (M.op x y)) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq763 eq179
    | exact resolve eq179 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1636 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq184 eq1634
    | exact resolve eq1634 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq1634
  have eq1787 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (M.op X2 (M.op X0 (M.op X1 (σ (M.op x y)))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq1026 eq14
    | exact resolve eq14 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1834 : ∀ X0 X1 X2 X3 : G, (σ y) = (M.op (σ y) (M.op X2 (M.op X3 (M.op X0 (M.op X1 (σ x)))))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1834_14 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (M.op X2 (M.op X0 (M.op X1 (σ (M.op x y)))))) ∨ x = (M.op x y) := by
      intro X0 X1 X2
      grind
    have f1834_15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op X0 (M.op X1 (σ x))) (σ (M.op x y))) ∨ x = (M.op x y) := by
      intro X0 X1
      grind
    have f1834_24 : (σ y) ≠ (M.op (σ y) (M.op X2 (M.op X3 (M.op X0 (M.op X1 (σ x)))))) := by grind
    have f1834_26 : x ≠ (M.op x y) := by grind
    have f1834_28 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op X0 (M.op X1 (σ x))) (σ (M.op x y))) := by
      intro X0 X1
      first
      | (have j0 := f1834_15 X0 X1
         grind)
      | (have r₁ := f1834_15 X0 X1
         have r₂ := f1834_26
         grind)
      | exact resolve f1834_15 f1834_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1834_29 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (M.op X2 (M.op X0 (M.op X1 (σ (M.op x y)))))) := by
      intro X0 X1 X2
      first
      | (have j0 := f1834_14 X0 X1 X2
         grind)
      | (have r₁ := f1834_14 X0 X1 X2
         have r₂ := f1834_26
         grind)
      | exact resolve f1834_14 f1834_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1834_83 : ∀ X0 X1 X2 X3 : G, (σ y) = (M.op (σ y) (M.op X2 (M.op X3 (M.op X0 (M.op X1 (σ x)))))) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f1834_29 X3 (M.op X0 (M.op X1 (σ x))) X2
         have i₂ := f1834_28 X0 X1
         grind)
      | exact superpose f1834_28 f1834_29
      | exact resolve f1834_29 f1834_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1834_194 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f1834_24
         have i₂ := f1834_83 X0 X1 X2 X3
         grind)
      | exact superpose f1834_83 f1834_24
      | (have r₁ := f1834_24
         have r₂ := f1834_83 X0 X1 X2 X3
         grind)
      | exact resolve f1834_24 f1834_83
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1834_204 : False := by grind
    exact f1834_204
  clear eq926 eq1787
  have eq1862 : ∀ X0 X1 X2 X3 : G, (σ y) = (M.op (σ y) (M.op X2 (M.op X3 (M.op X0 (M.op X1 (σ x)))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1834 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834
  have eq1994 : ∀ X0 X1 X2 : G, (σ x) = (M.op (σ x) (M.op X2 (M.op X0 (M.op X1 (σ y))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq630 eq297
    | exact resolve eq297 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq2009 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op X0 (M.op X1 (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq630 eq14
    | exact resolve eq14 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3719 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X3 (M.op X4 (M.op X5 (M.op X1 (M.op X2 X0)))))) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq564 (M.op X1 (M.op X2 X0)) X0 X2 X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq564
    | exact resolve eq564 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq4386 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq894 x y
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq894
    | (have j0 := eq894 x y
       grind)
    | exact resolve eq894 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq4409 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4386
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4386
    | exact resolve eq4386 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4386
  have eq4439 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4409
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4409
    | exact resolve eq4409 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4409
  have eq4467 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4439
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4439
    | exact resolve eq4439 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4439
  have eq4478 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4467
    | exact resolve eq4467 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467
  have eq4742 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k X0 y))) ∨ x = (M.op x y) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq233 eq942
    | (have j1 := eq233 X0
       grind)
    | exact resolve eq942 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq4753 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X1 (σ (k X0 y)))) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq233 eq14
    | (have j1 := eq233 X0
       grind)
    | exact resolve eq14 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq4778 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (k X0 (σ y))) ∨ x = (M.op x y) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4742 (τ X0)
       have i₂ := eq41 X0 y
       grind)
    | exact superpose eq41 eq4742
    | (have j0 := eq4742 (τ X0)
       grind)
    | exact resolve eq4742 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4742
  have eq4803 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (k X0 (σ y))) ∨ x = (M.op x y) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4778 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4778
    | (have j0 := eq4778 X0
       grind)
    | exact resolve eq4778 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4778
  have eq4810 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (k X0 (σ y))) ∨ (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4803 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4803
    | (have j0 := eq4803 X0
       grind)
    | exact resolve eq4803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq6526 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (σ X0)))) = (M.op (M.op X1 (M.op X2 (M.op X3 (σ X0)))) (M.op X4 (σ (k (M.op x y) X0)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq181 eq578
    | (have j1 := eq181 X0
       grind)
    | exact resolve eq578 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq578
  have eq7674 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq7746 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (σ (M.op X1 (M.op X2 (τ X0))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq770 X0 X1 X2
       have i₂ := eq358 X0
       grind)
    | exact superpose eq358 eq770
    | (have j0 := eq770 X0 X1 X2
       grind)
    | exact resolve eq770 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq770
  have eq7868 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (k (σ x) (σ (M.op X0 (M.op X1 x)))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq28 eq7746
    | exact resolve eq7746 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq7746
  have eq7925 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (σ (k x (M.op X0 (M.op X1 x)))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq42 eq7868
    | exact resolve eq7868 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq7868
  have eq9012 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ (M.op X2 (M.op x y))))) = (M.op (M.op X0 (M.op X1 (σ (M.op X2 (M.op x y))))) (σ (M.op y y))) ∨ (σ y) = (M.op (σ y) (σ (M.op X2 (M.op x y)))) ∨ y = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq130 eq891
    | (have j0 := eq891 y (M.op X2 (M.op x y)) X2 x
       grind)
    | exact resolve eq891 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq891
  have eq9108 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ (M.op X2 (M.op x y))))) = (M.op (M.op X0 (M.op X1 (σ (M.op X2 (M.op x y))))) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op X2 (M.op x y)))) ∨ y = (M.op y y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9012 X0 X1 X2
       have i₂ := eq147
       grind)
    | exact superpose eq147 eq9012
    | (have j0 := eq9012 X0 X1 X2
       grind)
    | exact resolve eq9012 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9012
  have eq9144 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (σ (M.op X2 (M.op x y)))) ∨ (M.op X0 (M.op X1 (σ (M.op X2 (M.op x y))))) = (M.op (M.op X0 (M.op X1 (σ (M.op X2 (M.op x y))))) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9108 X0 X1 X2
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9108
    | (have j0 := eq9108 X0 X1 X2
       grind)
    | exact resolve eq9108 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9108
  have eq16201 : (σ (k (M.op x y) y)) = (k (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq226
       have i₂ := eq949
       grind)
    | exact superpose eq949 eq226
    | exact resolve eq226 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq949
  have eq16259 : (k (σ (M.op x y)) (σ y)) = (k (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179 eq16201
    | exact resolve eq16201 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq16201
  have eq16277 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16259 eq4810
    | (have j0 := eq4810 (σ (M.op x y))
       grind)
    | exact resolve eq4810 eq16259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810 eq16259
  have eq16299 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq16277
  have eq17233 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16299 eq14
    | exact resolve eq14 eq16299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16299
  have eq20887 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17233 eq1862
    | exact resolve eq1862 eq17233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862 eq17233
  have eq20926 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | (have j0 := eq20887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20887
  have eq21063 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq20926 eq1994
    | exact resolve eq1994 eq20926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq21065 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq20926 eq2009
    | exact resolve eq2009 eq20926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20926
  have eq21103 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | (have j0 := eq21063 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21063
  have eq21398 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq21065
    | (have j0 := eq21065 (σ x)
       grind)
    | exact resolve eq21065 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21405 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq21065 eq2009
    | exact resolve eq2009 eq21065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009 eq21065
  have eq23469 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq21405 eq13
    | exact resolve eq13 eq21405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21405
  have eq23506 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | (have j0 := eq23469 X0
       grind)
    | (have r₁ := eq23469 X0
       have r₂ := eq21398
       grind)
    | exact resolve eq23469 eq21398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21398 eq23469
  have eq314021 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) ≠ (k (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq171 eq7674
    | (have j0 := eq7674 (σ x) (σ y)
       grind)
    | exact resolve eq7674 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq7674
  have eq316534 : ∀ X0 X1 : G, (σ x) ≠ (k (σ x) (M.op X0 (M.op X1 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq117 eq314021
    | exact resolve eq314021 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314021
  have eq316616 : ∀ X0 X1 : G, (σ x) ≠ (k (σ x) (M.op X0 (M.op X1 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq316534 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316534
  have eq316634 : ∀ X0 : G, (σ x) ≠ (k (σ x) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq865 eq316616
    | exact resolve eq316616 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq316616
  have eq316689 : ∀ X0 : G, (σ x) ≠ (k (σ x) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq316634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316634
  have eq316700 : ∀ X0 : G, (σ x) ≠ (k (σ x) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq316689 X0
       grind)
    | (have r₁ := eq316689 X0
       have r₂ := eq135
       grind)
    | exact resolve eq316689 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq316689
  have eq316792 : ∀ X0 X1 : G, (σ x) ≠ (k (σ x) (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1005 eq316700
    | exact resolve eq316700 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq316700
  have eq316829 : ∀ X0 X1 : G, (σ x) ≠ (k (σ x) (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq316792 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316792
  have eq316944 : ∀ X0 X1 X2 : G, (σ x) ≠ (k (σ x) (M.op X2 (M.op X0 (M.op X1 (σ y))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq630 eq316829
    | exact resolve eq316829 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq316829
  have eq318272 : ∀ X0 : G, (σ x) ≠ (k (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq21103 eq316944
    | exact resolve eq316944 eq21103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21103 eq316944
  have eq318301 : ∀ X0 : G, (σ x) ≠ (k (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | (have j0 := eq318272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318272
  have eq757318 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq117 eq23506
    | exact resolve eq23506 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq23506
  have eq757364 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | (have j0 := eq757318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757318
  have eq757365 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq757364 x
       have r₂ := eq318301 x
       grind)
    | exact resolve eq757364 eq318301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318301 eq757364
  have eq757366 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1636 eq757365
    | exact resolve eq757365 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757365
  have eq758913 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq757366 eq14
    | exact resolve eq14 eq757366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757366
  have eq759010 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq758913 eq1179
    | exact resolve eq1179 eq758913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq758913
  have eq759393 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq759010
    | exact resolve eq759010 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq759010
  have eq759394 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq759393
  have eq759420 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq759394 eq34
    | exact resolve eq34 eq759394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759394
  have eq759797 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq759420 eq1035
    | exact resolve eq1035 eq759420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq759420
  have eq760054 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq759797
  have eq760101 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq760054
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq760054
    | exact resolve eq760054 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq760054
  have eq760102 : x = (M.op x y) := by grind
  clear eq760101
  have eq760104 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq760102 eq20
    | exact resolve eq20 eq760102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq760105 : ∀ X0 : G, y = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq760102 eq34
    | exact resolve eq34 eq760102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq760134 : (M.op x x) = (k x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq760102 eq763
    | exact resolve eq763 eq760102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq760487 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq760104
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq760104
    | exact resolve eq760104 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760104
  have eq760516 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq760487 eq26
    | exact resolve eq26 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760530 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq760487 eq95
    | exact resolve eq95 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq760617 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq760487 eq4478
    | exact resolve eq4478 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478
  have eq761629 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq760617
       have r₂ := eq27
       grind)
    | exact resolve eq760617 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760617
  have eq761851 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1636 eq761629
    | exact resolve eq761629 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636 eq761629
  have eq761853 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq760102 eq761851
    | exact resolve eq761851 eq760102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761851
  have eq761872 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7925 y x
       have i₂ := eq760105 x
       grind)
    | exact superpose eq760105 eq7925
    | exact resolve eq7925 eq760105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7925 eq760105
  have eq761970 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq761872
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq761872
    | exact resolve eq761872 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761872
  have eq761972 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq760487 eq761970
    | exact resolve eq761970 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761970
  have eq787034 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq4753 x X0
       have i₂ := eq760134
       grind)
    | exact superpose eq760134 eq4753
    | (have j0 := eq4753 x x
       grind)
    | exact resolve eq4753 eq760134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4753 eq760134
  have eq787089 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq787034 X0
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq787034
    | exact resolve eq787034 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787034
  have eq787150 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq760487 eq787089
    | exact resolve eq787089 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787089
  have eq787211 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq787150 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq787150
    | (have j0 := eq787150 X0
       grind)
    | exact resolve eq787150 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787150
  have eq787265 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26 eq787211
    | (have j0 := eq787211 X0
       grind)
    | exact resolve eq787211 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq787211
  have eq787302 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq760487 eq787265
    | (have j0 := eq787265 X0
       grind)
    | exact resolve eq787265 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787265
  have eq787338 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq787302 X0
       grind)
    | (have r₁ := eq787302 X0
       have r₂ := eq27
       grind)
    | exact resolve eq787302 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787302
  have eq790318 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq761972 eq84
    | (have j0 := eq84 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq84 eq761972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq761972
  have eq790336 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq760516 eq790318
    | exact resolve eq790318 eq760516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790318
  have eq790351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq760516 eq790336
    | exact resolve eq790336 eq760516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790336
  have eq790362 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq790351
       have r₂ := eq27
       grind)
    | exact resolve eq790351 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790351
  have eq790540 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq790362 eq14
    | exact resolve eq14 eq790362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790362
  have eq806925 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (σ y)))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq787338 eq3719
    | exact resolve eq3719 eq787338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719 eq787338
  have eq830079 : (σ (k x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq760530 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq760530
    | (have j0 := eq760530 y
       grind)
    | exact resolve eq760530 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760530
  have eq830302 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq760516 eq830079
    | exact resolve eq830079 eq760516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830079
  have eq830583 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq830302
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq830302
    | exact resolve eq830302 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq830302
  have eq830758 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq760487 eq830583
    | exact resolve eq830583 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830583
  have eq830829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq760516 eq830758
    | exact resolve eq830758 eq760516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830758
  have eq830867 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq830829
       have r₂ := eq27
       grind)
    | exact resolve eq830829 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830829
  have eq830937 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq830867 eq1156
    | exact resolve eq1156 eq830867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq831053 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq760102 eq830937
    | exact resolve eq830937 eq760102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830937
  have eq859958 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (σ X0)))) = (M.op (M.op X1 (M.op X2 (M.op X3 (σ X0)))) (M.op X4 (σ (k x X0)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq760102 eq6526
    | (have j0 := eq6526 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq6526 eq760102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526
  have eq860631 : ∀ X0 X3 : G, (σ X0) = (M.op (σ X0) (M.op X3 (σ (k x X0)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq859958 X0 (σ X0) x x x
       have i₂ := eq14 (σ X0) x x
       grind)
    | exact superpose eq14 eq859958
    | (have j0 := eq859958 X0 x x X3 x
       grind)
    | exact resolve eq859958 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859958
  have eq1089243 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ (k x (τ X0))))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq860631 (τ X0) x
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq860631
    | exact resolve eq860631 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860631
  have eq1090499 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k (σ x) X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1089243 X0 X1
       have i₂ := eq45 X0 x
       grind)
    | exact superpose eq45 eq1089243
    | (have j0 := eq1089243 X0 X1
       grind)
    | exact resolve eq1089243 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1089243
  have eq1090749 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k (σ x) X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1090499 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1090499
    | (have j0 := eq1090499 X0 X1
       grind)
    | exact resolve eq1090499 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090499
  have eq1090896 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k (σ (M.op x y)) X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq760487 eq1090749
    | (have j0 := eq1090749 X0 X1
       grind)
    | exact resolve eq1090749 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090749
  have eq1091389 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (k (σ (M.op x y)) X0) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq1090896 eq14
    | (have j1 := eq1090896 X0 x
       grind)
    | exact resolve eq14 eq1090896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090896
  have eq1091826 : ∀ X0 X1 : G, (M.op X1 (k (σ (M.op x y)) (M.op X0 X1))) = X1 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1091389 eq14
    | (have j1 := eq1091389 (M.op X0 X1)
       grind)
    | exact resolve eq14 eq1091389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091389
  have eq1192585 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (σ (M.op X2 x))) ∨ (M.op X0 (M.op X1 (σ (M.op X2 (M.op x y))))) = (M.op (M.op X0 (M.op X1 (σ (M.op X2 (M.op x y))))) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq760102 eq9144
    | (have j0 := eq9144 X0 X1 X2
       grind)
    | exact resolve eq9144 eq760102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9144
  have eq1192586 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ (M.op X2 x)))) = (M.op (M.op X0 (M.op X1 (σ (M.op X2 x)))) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op X2 x))) ∨ y = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq760102 eq1192585
    | (have j0 := eq1192585 X0 X1 X2
       grind)
    | exact resolve eq1192585 eq760102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192585
  have eq1192673 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x x))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1192586 (σ x) x x
       have i₂ := eq1398 x x
       grind)
    | exact superpose eq1398 eq1192586
    | (have j0 := eq1192586 x x x
       grind)
    | exact resolve eq1192586 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398 eq1192586
  have eq1192867 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x x))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1192673
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1192673
    | exact resolve eq1192673 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192673
  have eq1192902 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x x))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq760487 eq1192867
    | exact resolve eq1192867 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192867
  have eq1192924 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1192902
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq1192902
    | exact resolve eq1192902 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1192902
  have eq1192937 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq760487 eq1192924
    | exact resolve eq1192924 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192924
  have eq2673377 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1192937 eq14
    | exact resolve eq14 eq1192937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192937
  have eq2673824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq760516 eq2673377
    | exact resolve eq2673377 eq760516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673377
  have eq2673844 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2673824
       have r₂ := eq27
       grind)
    | exact resolve eq2673824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673824
  have eq2673915 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2673844 eq806925
    | exact resolve eq806925 eq2673844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806925 eq2673844
  have eq2674376 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2673915
       have r₂ := eq761853
       grind)
    | exact resolve eq2673915 eq761853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761853 eq2673915
  have eq2675517 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq147
       have i₂ := eq2674376
       grind)
    | exact superpose eq2674376 eq147
    | exact resolve eq147 eq2674376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq2674376
  have eq2676038 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2675517
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2675517
    | exact resolve eq2675517 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2675517
  have eq2676529 : (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2676038 eq1091826
    | exact resolve eq1091826 eq2676038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091826 eq2676038
  have eq2676567 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq830867 eq2676529
    | exact resolve eq2676529 eq830867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830867 eq2676529
  have eq2676590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq760516 eq2676567
    | exact resolve eq2676567 eq760516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676567
  have eq2676599 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2676590
       have r₂ := eq27
       grind)
    | exact resolve eq2676590 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676590
  have eq2677202 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2676599 eq790540
    | exact resolve eq790540 eq2676599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790540 eq2676599
  have eq2677531 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq2677202
  have eq2677544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq760516 eq2677531
    | exact resolve eq2677531 eq760516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760516 eq2677531
  have eq2677552 : x = (M.op x x) := by
    first
    | (have r₁ := eq2677544
       have r₂ := eq27
       grind)
    | exact resolve eq2677544 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2677544
  have eq2677795 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq2677552
       grind)
    | exact superpose eq2677552 eq65
    | exact resolve eq65 eq2677552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq2677552
  have eq2678446 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq2677795
       have r₂ := eq1042
       grind)
    | exact resolve eq2677795 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq2677795
  have eq2678497 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2678446
       have i₂ := eq831053
       grind)
    | exact superpose eq831053 eq2678446
    | exact resolve eq2678446 eq831053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831053 eq2678446
  have eq2678528 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq760102 eq2678497
    | exact resolve eq2678497 eq760102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760102 eq2678497
  have eq2678589 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2678528 eq15
    | exact resolve eq15 eq2678528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678528
  have eq2679451 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2678589
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2678589
    | exact resolve eq2678589 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2678589
  have eq2679516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq760487 eq2679451
    | exact resolve eq2679451 eq760487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760487 eq2679451
  have eq2679549 : False := by grind
  exact eq2679549

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pyx_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq35
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq226 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq88 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq88 X0 X0
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq230 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq234 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq227 X0 X1
       have j1 := eq76 X1 (σ X0)
       grind)
    | (have r₁ := eq227 X0 X0
       have r₂ := eq76 X0 (σ X0)
       grind)
    | exact resolve eq227 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq235 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq230 X0 X1
       have j1 := eq76 X1 (σ X0)
       grind)
    | (have r₁ := eq230 X0 X0
       have r₂ := eq76 X0 (σ X0)
       grind)
    | exact resolve eq230 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq230
  have eq246 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq234
    | (have j0 := eq234 X0 X1
       grind)
    | exact resolve eq234 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq247 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq248 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq247 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq257 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq246
    | (have j0 := eq246 X0 X1
       grind)
    | exact resolve eq246 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq258 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq257 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq259 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq248
    | (have j0 := eq248 X0 X1
       grind)
    | exact resolve eq248 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq248
  have eq265 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       have j1 := eq258 X0 X1
       grind)
    | (have r₁ := eq259 X0 X1
       have r₂ := eq258 X0 X1
       grind)
    | exact resolve eq259 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq259
  have eq267 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq265
    | exact resolve eq265 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq265 x y
       grind)
    | exact superpose eq265 eq16
    | exact resolve eq16 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq369 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq267 X0 (τ X1)
       grind)
    | exact superpose eq267 eq18
    | exact resolve eq18 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq267
  have eq392 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq369
    | exact resolve eq369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq403 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq392
    | exact resolve eq392 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq430 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq278
       have i₂ := eq403 x y
       grind)
    | exact superpose eq403 eq278
    | exact resolve eq278 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq403
  have eq431 : False := by grind
  exact eq431

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pyx_pxx_pyx_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq41 X1 X1
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq41 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq41
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq43
  have eq93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq97 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq93 X1 X1
       have r₂ := eq48 X1 X1
       grind)
    | (have r₁ := eq93 X1 X0
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq93 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq93
  have eq211 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq97 (σ X1) (σ X0)
       grind)
    | exact superpose eq97 eq15
    | exact resolve eq15 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq97 X1 X0
       grind)
    | exact superpose eq97 eq211
    | exact resolve eq211 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq211
  have eq220 : False := by grind
  exact eq220

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq300 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq836 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ X1)) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq300 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq300
    | (have j0 := eq300 (σ X1) (σ X0)
       grind)
    | exact resolve eq300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq3521 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq87 (σ X1) X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3538 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq87 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq3539 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq3540 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3521 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521
  have eq3541 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3540 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3540
  have eq3543 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3539 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3539
    | (have j0 := eq3539 X0
       grind)
    | exact resolve eq3539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539
  have eq3582 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq3543 X0
       grind)
    | exact superpose eq3543 eq38
    | (have j1 := eq3543 X0
       grind)
    | exact resolve eq38 eq3543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3543
  have eq3595 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3582 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3582
    | (have j0 := eq3582 X0
       grind)
    | exact resolve eq3582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3582
  have eq3596 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3595 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3595
  have eq3598 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3596 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3596
    | exact resolve eq3596 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3621 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3596 X0
       grind)
    | exact superpose eq3596 eq11
    | exact resolve eq11 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596
  have eq3682 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3598 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq3598
    | exact resolve eq3598 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3598
  have eq3879 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3682 X0
       grind)
    | exact superpose eq3682 eq11
    | exact resolve eq11 eq3682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3989 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3879 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3879
    | exact resolve eq3879 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3879
  have eq4049 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq3989 (τ X0)
       grind)
    | exact superpose eq3989 eq34
    | exact resolve eq34 eq3989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4100 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4049 X0
       have i₂ := eq3682 X0
       grind)
    | exact superpose eq3682 eq4049
    | exact resolve eq4049 eq3682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3682 eq4049
  have eq4587 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4603 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4587 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4587
    | exact resolve eq4587 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq4639 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4603 X0
       have i₂ := eq3989 X0
       grind)
    | exact superpose eq3989 eq4603
    | exact resolve eq4603 eq3989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4603
  have eq4658 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq4639
  have eq24440 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) X0
       have i₂ := eq3541 (σ X0) X1
       grind)
    | exact superpose eq3541 eq24
    | (have j1 := eq3541 (σ X0) X1
       grind)
    | exact resolve eq24 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3541
  have eq24522 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24440 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq24440
    | (have j0 := eq24440 X0 X1
       grind)
    | exact resolve eq24440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24440
  have eq24600 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24522 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24522
    | (have j0 := eq24522 X0 X1
       grind)
    | exact resolve eq24522 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24522
  have eq24669 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24600 X0 X1
       have i₂ := eq3621 X0
       grind)
    | exact superpose eq3621 eq24600
    | (have j0 := eq24600 X0 X1
       grind)
    | exact resolve eq24600 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24600
  have eq24716 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24669 X0 X1
       have i₂ := eq3989 X0
       grind)
    | exact superpose eq3989 eq24669
    | (have j0 := eq24669 X0 X1
       grind)
    | exact resolve eq24669 eq3989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24669
  have eq24754 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24716 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24716
    | (have j0 := eq24716 X0 X1
       grind)
    | exact resolve eq24716 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24716
  have eq29480 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24754 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24754
    | (have j0 := eq24754 X1 (τ X0)
       grind)
    | exact resolve eq24754 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29534 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq24754 X1 X0
       grind)
    | exact superpose eq24754 eq11
    | (have j1 := eq24754 X1 X0
       grind)
    | exact resolve eq11 eq24754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24754
  have eq30245 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29480 X1 (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq29480
    | (have j0 := eq29480 X0 (τ X1)
       grind)
    | exact resolve eq29480 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29480
  have eq30430 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30245 X0 X1
       have i₂ := eq4100 X1
       grind)
    | exact superpose eq4100 eq30245
    | (have j0 := eq30245 X0 X1
       grind)
    | exact resolve eq30245 eq4100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100 eq30245
  have eq30512 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30430 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq30430
    | (have j0 := eq30430 X0 X1
       grind)
    | exact resolve eq30430 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30430
  have eq30586 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30512 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq30512
    | (have j0 := eq30512 X0 X1
       grind)
    | exact resolve eq30512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30512
  have eq30979 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30586 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30586
  have eq31308 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq836 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq836
    | (have j0 := eq836 (τ X0) (τ X1)
       grind)
    | exact resolve eq836 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq836
  have eq31385 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31308 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq31308
    | (have j0 := eq31308 X0 X1
       grind)
    | exact resolve eq31308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31308
  have eq31441 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31385 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq31385
    | (have j0 := eq31385 X0 X1
       grind)
    | exact resolve eq31385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31385
  have eq31495 : ∀ X0 X1 : G, (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31441 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31441
    | (have j0 := eq31441 X0 X1
       grind)
    | exact resolve eq31441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31441
  have eq31546 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31495 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31495
    | (have j0 := eq31495 X0 X1
       grind)
    | exact resolve eq31495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31495
  have eq31587 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31546 X0 X1
       have i₂ := eq3621 (σ (τ X1))
       grind)
    | exact superpose eq3621 eq31546
    | (have j0 := eq31546 X0 X1
       grind)
    | exact resolve eq31546 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621 eq31546
  have eq31625 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31587 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq31587
    | (have j0 := eq31587 X0 X1
       grind)
    | exact resolve eq31587 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31587
  have eq31661 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31625 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq31625
    | (have j0 := eq31625 X0 X1
       grind)
    | exact resolve eq31625 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq31625
  have eq31690 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31661 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq31661
    | (have j0 := eq31661 X0 X1
       grind)
    | exact resolve eq31661 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31661
  have eq31715 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31690 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31690
    | (have j0 := eq31690 X0 X1
       grind)
    | exact resolve eq31690 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31690
  have eq31740 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31715 X0 X1
       have i₂ := eq3989 X1
       grind)
    | exact superpose eq3989 eq31715
    | (have j0 := eq31715 X0 X1
       grind)
    | exact resolve eq31715 eq3989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989 eq31715
  have eq34788 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29534 y x
       grind)
    | exact superpose eq29534 eq16
    | (have j1 := eq29534 y x
       grind)
    | exact resolve eq16 eq29534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29534
  have eq35801 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34788
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq34788
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq34788 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34788
  have eq35804 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq35801
  have eq35805 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq35804
  have eq35808 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30979 y x
       have i₂ := eq35805
       grind)
    | exact superpose eq35805 eq30979
    | (have j0 := eq30979 y x
       grind)
    | exact resolve eq30979 eq35805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30979
  have eq35812 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq35808
  have eq35813 : y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq35812
  have eq36375 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4658 x
       have i₂ := eq35813
       grind)
    | exact superpose eq35813 eq4658
    | exact resolve eq4658 eq35813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35813
  have eq36398 : (σ y) = (σ (M.op x x)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq36375
       have r₂ := eq16
       grind)
    | exact resolve eq36375 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36375
  have eq36935 : (M.op x x) = (τ (σ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq36398
       grind)
    | exact superpose eq36398 eq10
    | exact resolve eq10 eq36398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36398
  have eq37065 : y = (M.op x x) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq36935
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq36935
    | exact resolve eq36935 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36935
  have eq37153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq4658 x
       have i₂ := eq37065
       grind)
    | exact superpose eq37065 eq4658
    | exact resolve eq4658 eq37065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37065
  have eq37176 : (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq37153
       have r₂ := eq16
       grind)
    | exact resolve eq37153 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37153
  have eq37708 : (k y x) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq37176
       grind)
    | exact superpose eq37176 eq11
    | exact resolve eq11 eq37176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37176
  have eq37890 : x = (k y x) := by
    first
    | (have i₁ := eq37708
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq37708
    | exact resolve eq37708 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37708
  have eq37968 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq31740 y x
       have i₂ := eq37890
       grind)
    | exact superpose eq37890 eq31740
    | (have j0 := eq31740 y x
       grind)
    | exact resolve eq31740 eq37890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31740 eq37890
  have eq37969 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq37968
  have eq41462 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37969
       grind)
    | exact superpose eq37969 eq16
    | exact resolve eq16 eq37969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37969
  have eq42042 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41462
       have i₂ := eq35805
       grind)
    | exact superpose eq35805 eq41462
    | exact resolve eq41462 eq35805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35805 eq41462
  have eq42043 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq42042
  have eq42044 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq42043
  have eq42067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4658 x
       have i₂ := eq42044
       grind)
    | exact superpose eq42044 eq4658
    | exact resolve eq4658 eq42044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42044
  have eq42091 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq42067
       have r₂ := eq16
       grind)
    | exact resolve eq42067 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42067
  have eq42671 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq42091
       grind)
    | exact superpose eq42091 eq10
    | exact resolve eq10 eq42091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42091
  have eq42803 : y = (M.op x x) := by
    first
    | (have i₁ := eq42671
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq42671
    | exact resolve eq42671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42671
  have eq42914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4658 x
       have i₂ := eq42803
       grind)
    | exact superpose eq42803 eq4658
    | exact resolve eq4658 eq42803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4658 eq42803
  have eq42937 : False := by grind
  exact eq42937

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq17
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
  have eq263 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq263 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq263 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq263 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq275 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq264 (σ X0)
       grind)
    | exact superpose eq264 eq15
    | exact resolve eq15 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq264 (τ X0)
       grind)
    | exact superpose eq264 eq31
    | exact resolve eq31 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq281
    | exact resolve eq281 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq294 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq275
    | exact resolve eq275 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq275
  have eq337 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq294
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq294 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X2 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq462 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq485 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq471 X0 X1
       have j1 := eq337 X0 X1
       grind)
    | (have r₁ := eq471 X0 X1
       have r₂ := eq337 X0 X1
       grind)
    | exact resolve eq471 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq471
  have eq501 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq485 X1 (σ X0)
       grind)
    | exact superpose eq485 eq15
    | (have j1 := eq485 X1 (σ X0)
       grind)
    | exact resolve eq15 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq520 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq501 X0 X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq501
    | (have j0 := eq501 X0 X1
       grind)
    | exact resolve eq501 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq3798 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X2 X1) = (M.op X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq479 X1 X2 X0
       grind)
    | (have i₁ := eq13 X2 X2
       have i₂ := eq479 X0 X1 X2
       grind)
    | exact superpose eq479 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq479 X1 X2 X2
       grind)
    | (have r₁ := eq13 X2 X0
       have r₂ := eq479 X0 X1 X2
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq479 X0 X1 X0
       grind)
    | exact resolve eq13 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq3824 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X2 X1) = (M.op X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3798 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3798
  have eq3841 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3824 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq3824 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq3824 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3824
  have eq4080 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq520 x y
       grind)
    | exact superpose eq520 eq16
    | (have j1 := eq520 x y
       grind)
    | exact resolve eq16 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4104 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq4144 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4104 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq4104
    | (have j0 := eq4104 (τ X0) (τ X1)
       grind)
    | exact resolve eq4104 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq4206 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4144 X0 X1
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq4144
    | (have j0 := eq4144 X0 X1
       grind)
    | exact resolve eq4144 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144
  have eq4234 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4206 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4206
    | (have j0 := eq4206 X0 X1
       grind)
    | exact resolve eq4206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4206
  have eq4258 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4234 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4234
    | (have j0 := eq4234 X0 X1
       grind)
    | exact resolve eq4234 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4234
  have eq4278 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4258 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4258
    | (have j0 := eq4258 X0 X1
       grind)
    | exact resolve eq4258 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4258
  have eq4293 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4278 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4278
    | (have j0 := eq4278 X0 X1
       grind)
    | exact resolve eq4278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278
  have eq4306 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4293 X0 X1
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq4293
    | (have j0 := eq4293 X0 X1
       grind)
    | exact resolve eq4293 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq4293
  have eq4315 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4306 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4306
    | (have j0 := eq4306 X0 X1
       grind)
    | exact resolve eq4306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4306
  have eq10332 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3841 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3841
  have eq10333 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq10332 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10332
  have eq10479 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq4080
       have i₂ := eq10333 x y
       grind)
    | exact superpose eq10333 eq4080
    | (have j1 := eq10333 x y
       grind)
    | exact resolve eq4080 eq10333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4080
  have eq10480 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq10333 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10333
  have eq10481 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k x y) := by grind
  clear eq10479
  have eq10649 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq10480 (σ x) (σ y)
       have i₂ := eq10481
       grind)
    | exact superpose eq10481 eq10480
    | (have j0 := eq10480 (σ x) (σ y)
       grind)
    | exact resolve eq10480 eq10481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10481
  have eq10656 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x x) = (k x y) := by
    first
    | (have r₁ := eq10649
       have r₂ := eq294 x
       grind)
    | exact resolve eq10649 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10649
  have eq10658 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq10656
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq10656
    | exact resolve eq10656 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10656
  have eq10660 : (M.op x x) = (k x y) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10658
       have i₂ := eq294 x
       grind)
    | exact superpose eq294 eq10658
    | exact resolve eq10658 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10658
  have eq10682 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq4104 x y
       have i₂ := eq10660
       grind)
    | exact superpose eq10660 eq4104
    | (have j0 := eq4104 x y
       grind)
    | (have r₁ := eq4104 x y
       have r₂ := eq10660
       grind)
    | exact resolve eq4104 eq10660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10660
  have eq10693 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq10682
  have eq10696 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq4104 x y
       grind)
    | (have r₁ := eq10693
       have r₂ := eq4104 x y
       grind)
    | exact resolve eq10693 eq4104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104 eq10693
  have eq10701 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10696
       grind)
    | exact superpose eq10696 eq16
    | exact resolve eq16 eq10696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10703 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq10480 (σ x) (σ y)
       have i₂ := eq10696
       grind)
    | exact superpose eq10696 eq10480
    | (have j0 := eq10480 (σ x) (σ y)
       grind)
    | exact resolve eq10480 eq10696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10480 eq10696
  have eq10710 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq10703
       have r₂ := eq294 x
       grind)
    | exact resolve eq10703 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10703
  have eq10712 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10710
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq10710
    | exact resolve eq10710 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10710
  have eq10714 : (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10712
       have i₂ := eq294 x
       grind)
    | exact superpose eq294 eq10712
    | exact resolve eq10712 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq10712
  have eq10729 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq10714
       grind)
    | exact superpose eq10714 eq10
    | exact resolve eq10 eq10714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10714
  have eq10785 : (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq10729
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq10729
    | exact resolve eq10729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10729
  have eq10804 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4315 x y
       have i₂ := eq10785
       grind)
    | exact superpose eq10785 eq4315
    | (have j0 := eq4315 x y
       grind)
    | (have r₁ := eq4315 x y
       have r₂ := eq10785
       grind)
    | exact resolve eq4315 eq10785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315 eq10785
  have eq10813 : (M.op x y) = (M.op x x) := by grind
  clear eq10804
  have eq10817 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10701
       have i₂ := eq10813
       grind)
    | exact superpose eq10813 eq10701
    | exact resolve eq10701 eq10813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10701 eq10813
  have eq10826 : False := by grind
  exact eq10826

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X0) X1))) = X0 := by
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
  have eq66 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq69 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq66
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq66
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq66 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq107 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq108 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq114 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq43
    | exact resolve eq43 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq121 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq114
    | exact resolve eq114 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq114
  have eq747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq99 eq69
    | (have j0 := eq69 (σ y) (σ x)
       grind)
    | exact resolve eq69 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq747
    | exact resolve eq747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq751 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq748
       have r₂ := eq27
       grind)
    | exact resolve eq748 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq753 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq751
    | exact resolve eq751 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq755 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq753 eq108
    | (have r₁ := eq108
       have r₂ := eq753
       grind)
    | exact resolve eq108 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq760 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq753 eq14
    | exact resolve eq14 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq755
  have eq870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq763 eq99
    | exact resolve eq99 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq870
  have eq875 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq873
       have r₂ := eq27
       grind)
    | exact resolve eq873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq878 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq107
    | (have r₁ := eq107
       have r₂ := eq875
       grind)
    | exact resolve eq107 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq121
    | exact resolve eq121 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq882 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq886 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq878
  have eq888 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq879
    | exact resolve eq879 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq952 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq886
       grind)
    | exact superpose eq886 eq66
    | exact resolve eq66 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq954 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq952
    | exact resolve eq952 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq954 eq69
    | (have j0 := eq69 (σ y) (σ x)
       grind)
    | exact resolve eq69 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq959
    | exact resolve eq959 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq965 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq962
       have r₂ := eq27
       grind)
    | exact resolve eq962 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq967 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq965
    | exact resolve eq965 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq1020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq967 eq888
    | exact resolve eq888 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq1033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1020
  have eq1036 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1033
       have r₂ := eq27
       grind)
    | exact resolve eq1033 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1201 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq882 X0
       grind)
    | (have r₁ := eq882 X0
       have r₂ := eq1036
       grind)
    | exact resolve eq882 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq1036
  have eq1208 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq1201 y
       grind)
    | exact superpose eq1201 eq66
    | exact resolve eq66 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1225 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1208
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1208
    | exact resolve eq1208 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1208
  have eq1227 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1225
    | exact resolve eq1225 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1227 eq69
    | (have j0 := eq69 (σ y) (σ x)
       grind)
    | exact resolve eq69 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1232
    | exact resolve eq1232 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1238 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1235
       have r₂ := eq27
       grind)
    | exact resolve eq1235 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1240 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1238
    | exact resolve eq1238 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1240 eq888
    | exact resolve eq888 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq1240
  have eq1318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1305
  have eq1321 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1318
       have r₂ := eq27
       grind)
    | exact resolve eq1318 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1324 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1321 eq27
    | exact resolve eq27 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1601 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op (σ x) X0))) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1321 eq760
    | exact resolve eq760 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq1606 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq753 eq1601
    | exact resolve eq1601 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq1613 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1606
  have eq1614 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1321 eq1613
    | exact resolve eq1613 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321 eq1613
  have eq1677 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1614 eq1601
    | exact resolve eq1601 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601 eq1614
  have eq1679 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1677
  have eq1695 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1679 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1679
       grind)
    | exact resolve eq13 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679
  have eq1697 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq1976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1697 eq99
    | exact resolve eq99 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1697
  have eq1986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1976
  have eq1992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq1986
    | exact resolve eq1986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986
  have eq1996 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1992
       have r₂ := eq27
       grind)
    | exact resolve eq1992 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq2119 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq1996
       grind)
    | exact superpose eq1996 eq107
    | (have r₁ := eq107
       have r₂ := eq1996
       grind)
    | exact resolve eq107 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq2120 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq1996
       grind)
    | exact superpose eq1996 eq121
    | exact resolve eq121 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq1996
  have eq2127 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq2119
  have eq2129 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq2120
    | exact resolve eq2120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq2280 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq2127
       grind)
    | exact superpose eq2127 eq66
    | exact resolve eq66 eq2127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2127
  have eq2283 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2280
    | exact resolve eq2280 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280
  have eq2290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2283 eq69
    | (have j0 := eq69 (σ y) (σ x)
       grind)
    | exact resolve eq69 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2283
  have eq2291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2290
    | exact resolve eq2290 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2294 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2291
       have r₂ := eq27
       grind)
    | exact resolve eq2291 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291
  have eq2296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2129 eq2294
    | exact resolve eq2294 eq2129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129 eq2294
  have eq2298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2296
    | exact resolve eq2296 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2296
  have eq2300 : x = (M.op x y) := by
    first
    | (have r₁ := eq2298
       have r₂ := eq27
       grind)
    | exact resolve eq2298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2298
  have eq2302 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2300 eq20
    | exact resolve eq20 eq2300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2300
  have eq2336 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2302
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2302
    | exact resolve eq2302 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2302
  have eq2340 : False := by grind
  exact eq2340

/-- `Equation633`: `x = x ◇ (y ◇ ((x ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pyx_Equation633 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law633 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law633.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X1) X1))) = X0 := by
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
  have eq53 : x = (M.op x (M.op y (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
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
  clear eq52
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq12158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12159 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq12158
    | exact resolve eq12158 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12158
  have eq12170 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq12159
       have r₂ := eq28
       grind)
    | exact resolve eq12159 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12159
  have eq12174 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq12170 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12170
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12170
       grind)
    | exact resolve eq12 eq12170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12170
  have eq12182 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq12174
  have eq12183 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq12182
  have eq12305 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq12183 eq102
    | exact resolve eq102 eq12183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq12306 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq12183 eq104
    | exact resolve eq104 eq12183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq12183
  have eq12320 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12306
  have eq12329 : x = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq29 eq12305
    | exact resolve eq12305 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12305
  have eq12334 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq12 x (k y x)
       grind)
    | (have r₁ := eq12329
       have r₂ := eq12 y x
       grind)
    | exact resolve eq12329 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12329
  have eq12336 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq12334
       grind)
    | exact superpose eq12334 eq90
    | exact resolve eq90 eq12334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq12334
  have eq12362 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12336
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12336
    | exact resolve eq12336 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12336
  have eq12412 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12362 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12362
  have eq12413 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12412
  have eq12418 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12413
    | exact resolve eq12413 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12413
  have eq12556 : y = (M.op y (M.op x (M.op y x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq12320
       grind)
    | exact superpose eq12320 eq14
    | exact resolve eq14 eq12320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12815 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12418 eq14
    | exact resolve eq14 eq12418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18509 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12556
       have i₂ := eq12320
       grind)
    | exact superpose eq12320 eq12556
    | exact resolve eq12556 eq12320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12320 eq12556
  have eq18519 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18509
  have eq18521 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18519
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18519
    | exact resolve eq18519 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18519
  have eq18681 : y = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18521 eq14
    | exact resolve eq14 eq18521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20950 : y = (M.op y (M.op (M.op x y) y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18521 eq18681
    | exact resolve eq18681 eq18521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18521 eq18681
  have eq20960 : y = (M.op y (M.op (M.op x y) y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20950
  have eq21126 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20960 eq53
    | exact resolve eq53 eq20960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq20960
  have eq21137 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21126
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21126
    | exact resolve eq21126 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21126
  have eq21139 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21137 eq30
    | exact resolve eq30 eq21137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21137
  have eq21260 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq21139
    | exact resolve eq21139 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21139
  have eq21261 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq21260
  have eq21281 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21261 eq29
    | exact resolve eq29 eq21261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21261
  have eq21488 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq21281
    | exact resolve eq21281 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21281
  have eq21489 : x = (M.op x y) ∨ x = y := by grind
  clear eq21488
  have eq21508 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21489 eq21
    | exact resolve eq21 eq21489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21670 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq21508
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21508
    | exact resolve eq21508 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21508
  have eq21691 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21670 eq27
    | exact resolve eq27 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21767 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21670 eq12418
    | exact resolve eq12418 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12418
  have eq21768 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21670 eq12815
    | exact resolve eq12815 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12815
  have eq21825 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq21768
  have eq21826 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq21767
  have eq21839 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq21825
       have r₂ := eq28
       grind)
    | exact resolve eq21825 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21825
  have eq21840 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq21826
       have r₂ := eq28
       grind)
    | exact resolve eq21826 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21826
  have eq1631891 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21840 eq21839
    | exact resolve eq21839 eq21840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21839 eq21840
  have eq1631917 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1631891
  have eq1631920 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21691 eq1631917
    | exact resolve eq1631917 eq21691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21691 eq1631917
  have eq1631946 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1631920
  have eq1631951 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1631946 eq14
    | exact resolve eq14 eq1631946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1797226 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1631946 eq1631951
    | exact resolve eq1631951 eq1631946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631946 eq1631951
  have eq1797254 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1797226
  have eq1797257 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1797254 eq54
    | exact resolve eq54 eq1797254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1797254
  have eq1797298 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1797257
    | exact resolve eq1797257 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797257
  have eq1797299 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1797298 eq28
    | exact resolve eq28 eq1797298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797298
  have eq1797348 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1797299
       have r₂ := eq21670
       grind)
    | exact resolve eq1797299 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21670 eq1797299
  have eq1797367 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1797348 eq30
    | exact resolve eq30 eq1797348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1797348
  have eq1798910 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1797367
    | exact resolve eq1797367 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1797367
  have eq1799245 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1798910 eq21489
    | exact resolve eq21489 eq1798910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21489 eq1798910
  have eq1800464 : x = y := by grind
  clear eq1799245
  have eq1800904 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1800464
       grind)
    | exact superpose eq1800464 eq19
    | exact resolve eq19 eq1800464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1800905 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1800464
       grind)
    | exact superpose eq1800464 eq25
    | exact resolve eq25 eq1800464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1800464
  have eq1801338 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1800905
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1800905
    | exact resolve eq1800905 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1800905
  have eq1801372 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1801338 eq27
    | exact resolve eq27 eq1801338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1801338
  have eq1802598 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1801372 eq68
    | exact resolve eq68 eq1801372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1801372
  have eq1802696 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1802598
       have i₂ := eq1800904
       grind)
    | exact superpose eq1800904 eq1802598
    | exact resolve eq1802598 eq1800904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800904 eq1802598
  have eq1802708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1802696 eq15
    | exact resolve eq15 eq1802696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802696
  have eq1803552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1802708
    | exact resolve eq1802708 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1802708
  have eq1803734 : False := by grind
  exact eq1803734

/-- `Equation649`: `x = x ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_x_pxy_pxx_pxy_Equation649 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law649 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law649.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq50 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X0) X0)) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op (M.op X2 X0) X0)) X3 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X0) X0)) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq43
    | exact resolve eq43 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq49
    | exact resolve eq49 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq68
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq68
    | exact resolve eq68 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq70 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq75
    | (have j0 := eq75 (σ X0) (σ X1)
       grind)
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq75
    | (have j0 := eq75 (σ x) (σ X0)
       grind)
    | exact resolve eq75 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq44
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq44 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq99 : (τ (σ (M.op x y))) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97 eq58
    | exact resolve eq58 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97 eq75
    | (have j0 := eq75 (σ x) (σ y)
       grind)
    | exact resolve eq75 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq100
    | exact resolve eq100 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq99
    | exact resolve eq99 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq104 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq101
       have r₂ := eq27
       grind)
    | exact resolve eq101 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq106 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq104
    | exact resolve eq104 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq108 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106 eq27
    | exact resolve eq27 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : x ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq111 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 (M.op (M.op X2 X0) X0))) ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op (M.op X2 X0) X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op (M.op X2 X0) X0))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op (M.op X2 X0) X0))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 (M.op (M.op X2 X0) X0))) ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq111 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq119 : (σ (k y (k x x))) = (k (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq36
    | exact resolve eq36 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq124 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq127 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq64 sF3
       grind)
    | exact superpose eq64 eq123
    | exact resolve eq123 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (k (σ y) (M.op (σ x) (σ x))) = (σ (k y (k x x))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq119
    | exact resolve eq119 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq129 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq64 y
       grind)
    | exact superpose eq64 eq127
    | exact resolve eq127 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq130 : (σ (k y (M.op x x))) = (k (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq128
    | exact resolve eq128 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq137 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq158 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : (σ (k x (M.op y y))) = (k (σ x) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq35 (M.op y y)
       have i₂ := eq129
       grind)
    | exact superpose eq129 eq35
    | exact resolve eq35 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq162 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op y y)
       have i₂ := eq129
       grind)
    | exact superpose eq129 eq10
    | exact resolve eq10 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq129
       grind)
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq137 eq16
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq253 : ∀ X0 : G, y ≠ y ∨ (M.op y y) = (M.op (M.op X0 (M.op (M.op x y) y)) (M.op X0 (M.op (M.op x y) y))) ∨ (M.op y y) = (k y (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq50 eq12
    | (have j0 := eq12 y (M.op X0 (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq12 y (M.op X0 (M.op (M.op x y) y))
       have r₂ := eq50 X0
       grind)
    | exact resolve eq12 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op (M.op x y) y)) (M.op X0 (M.op (M.op x y) y))) ∨ (M.op y y) = (k y (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have j0 := eq253 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq258 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106 eq51
    | exact resolve eq51 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq258
    | (have j0 := eq258 X0
       grind)
    | exact resolve eq258 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq265 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106 eq264
    | exact resolve eq264 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264 eq14
    | exact resolve eq14 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq264 eq14
    | exact resolve eq14 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq289 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq302 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq266 eq12
    | (have j0 := eq12 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq266
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq266
       grind)
    | exact resolve eq12 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq302
  have eq312 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106 eq304
    | exact resolve eq304 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq315 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq312
  have eq351 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq315 eq97
    | exact resolve eq97 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq315 eq58
    | exact resolve eq58 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq315
  have eq354 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq351
  have eq357 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq69 eq352
    | exact resolve eq352 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq408 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq357
       grind)
    | exact superpose eq357 eq102
    | exact resolve eq102 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq357
  have eq411 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq408
  have eq436 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq264 eq268
    | exact resolve eq268 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq444 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq436 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq483 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq106 eq444
    | exact resolve eq444 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq444
    | (have j0 := eq444 X0 (σ x)
       grind)
    | exact resolve eq444 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq354 eq444
    | exact resolve eq444 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq444
  have eq511 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq514 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq496 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq519 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f519_14 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f519_20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f519_23 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) := by grind
    have f519_24 : x ≠ (M.op x y) := by grind
    have f519_26 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
      intro X0
      first
      | (have j0 := f519_14 X0
         grind)
      | (have r₁ := f519_14 X0
         have r₂ := f519_24
         grind)
      | exact resolve f519_14 f519_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f519_92 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) := by
      intro X0 X1
      first
      | (have i₁ := f519_20 (M.op (σ x) (σ y)) X1 X0
         have i₂ := f519_26 X0
         grind)
      | exact superpose f519_26 f519_20
      | exact resolve f519_20 f519_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f519_224 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) := by
      first
      | (have i₁ := f519_23
         have i₂ := f519_92 X0 X1
         grind)
      | exact superpose f519_92 f519_23
      | (have r₁ := f519_23
         have r₂ := f519_92 X0 X1
         grind)
      | exact resolve f519_23 f519_92
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f519_233 : False := by grind
    exact f519_233
  clear eq500
  have eq574 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X4 X2))) = (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X4 X2))) (M.op X5 (M.op X4 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq54 (M.op X3 X0) X1 (M.op X1 (M.op (M.op X2 X0) X0)) X3
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y (M.op X1 (M.op (M.op x y) y)))) = (M.op (M.op X0 (M.op y (M.op X1 (M.op (M.op x y) y)))) (M.op X2 (M.op X1 (M.op (M.op x y) y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq54
    | exact resolve eq54 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ y) (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))))) = (M.op (M.op X0 (M.op (σ y) (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))))) (M.op X2 (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 (M.op X3 (M.op (M.op X4 X0) X0))) (M.op X3 (M.op (M.op X4 X0) X0)))) = (M.op (M.op X1 (M.op (M.op X2 (M.op X3 (M.op (M.op X4 X0) X0))) (M.op X3 (M.op (M.op X4 X0) X0)))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 (M.op X3 (M.op (M.op X4 X0) X0)) X1 X2 X0
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 (σ X1)) (σ X1))) = (M.op (M.op X2 (M.op (M.op X3 (σ X1)) (σ X1))) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (σ X1) X2 X3 (σ X0)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq54
    | (have j1 := eq81 X0 X1
       grind)
    | exact resolve eq54 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq617 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) y)) = (M.op (M.op X0 (M.op (M.op X1 y) y)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 y X0 X1 x
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op X3 X2) (M.op X4 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X3 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X3 X2) X4 (M.op X0 (M.op (M.op X1 X2) X2))
       have i₂ := eq54 X2 X0 X1 X3
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op X3 X2) (M.op X4 (M.op X0 (M.op (M.op X1 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq640 X0 X1 X2 X3 X4
       have i₂ := eq54 X2 X0 X1 X3
       grind)
    | exact superpose eq54 eq640
    | exact resolve eq640 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq644 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (M.op X2 (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq585
    | exact resolve eq585 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq585
  have eq645 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (M.op X0 y) (M.op X2 (M.op X1 (M.op (M.op x y) y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq580
    | exact resolve eq580 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq646 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X2) X2))) = (M.op (M.op X3 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op X5 (M.op X4 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq574 X1 X2 X0 X3 X3 X5
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq574
    | exact resolve eq574 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq652 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq514
    | (have j0 := eq514 X0 (σ x)
       grind)
    | exact resolve eq514 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq673 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq652 eq519
    | exact resolve eq519 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq652
  have eq688 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq737 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 (M.op X2 (M.op (M.op X3 X0) X0))) = (M.op X1 (M.op X2 (M.op (M.op X3 X0) X0))) ∨ (M.op X0 X0) = (k X0 (M.op X2 (M.op (M.op X3 X0) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X1 (M.op X2 (M.op (M.op X3 X0) X0))
       have i₂ := eq112 X0 X2 X3
       grind)
    | exact superpose eq112 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq112 X0 X2 X3
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op (M.op X2 X0) X0))
       have r₂ := eq112 X0 X1 X2
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op (M.op X2 X0) X0)) X0
       have r₂ := eq112 X0 X1 X2
       grind)
    | exact resolve eq13 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1593 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq289 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq289
    | exact resolve eq289 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1602 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq289
    | (have j0 := eq289 X0 (M.op x y)
       grind)
    | exact resolve eq289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq1617 : ∀ X0 : G, (τ (k X0 (M.op (σ x) (σ x)))) = (k (τ X0) (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1593 X0
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq1593
    | exact resolve eq1593 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1619 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq1617 X0
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq1617
    | exact resolve eq1617 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq1893 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq511 eq688
    | exact resolve eq688 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq1911 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1893 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq1932 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1911 eq14
    | exact resolve eq14 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq1993 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106 eq1932
    | exact resolve eq1932 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq2041 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1993
  have eq2228 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2041 eq69
    | exact resolve eq69 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041
  have eq2275 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq2228
    | exact resolve eq2228 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2228
  have eq2517 : (τ (σ (M.op x y))) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2275 eq69
    | exact resolve eq69 eq2275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2275
  have eq2562 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq2517
    | exact resolve eq2517 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2517
  have eq4443 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (M.op X1 (M.op X2 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq106 eq644
    | exact resolve eq644 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq4471 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (M.op X1 (M.op X2 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq26 eq4443
    | (have j0 := eq4443 X0 X1 X2
       grind)
    | exact resolve eq4443 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq4526 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | exact superpose eq50 eq645
    | exact resolve eq645 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq5214 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op x y) (M.op X2 (M.op (M.op X0 (M.op (M.op X1 y) y)) (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq617 eq14
    | exact resolve eq14 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5216 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op x y) (M.op X2 (M.op X0 (M.op (M.op X1 y) y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq617 eq5214
    | exact resolve eq5214 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214
  have eq5595 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq642 x x X0 X1 X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq642
    | exact resolve eq642 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq5931 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq264 eq4471
    | exact resolve eq4471 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq4471
  have eq5956 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5931
  have eq5994 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X1 (M.op X0 (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f5994_14 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f5994_20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f5994_23 : (σ y) ≠ (M.op (σ y) (M.op X1 (M.op X0 (σ y)))) := by grind
    have f5994_24 : x ≠ (M.op x y) := by grind
    have f5994_26 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
      intro X0
      first
      | (have j0 := f5994_14 X0
         grind)
      | (have r₁ := f5994_14 X0
         have r₂ := f5994_24
         grind)
      | exact resolve f5994_14 f5994_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5994_58 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X1 (M.op X0 (σ y)))) := by
      intro X0 X1
      first
      | (have i₁ := f5994_20 (σ y) X1 X0
         have i₂ := f5994_26 X0
         grind)
      | exact superpose f5994_26 f5994_20
      | exact resolve f5994_20 f5994_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5994_106 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f5994_23
         have i₂ := f5994_58 X0 X1
         grind)
      | exact superpose f5994_58 f5994_23
      | (have r₁ := f5994_23
         have r₂ := f5994_58 X0 X1
         grind)
      | exact resolve f5994_23 f5994_58
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5994_111 : False := by grind
    exact f5994_111
  clear eq5956
  have eq6048 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq411 eq5994
    | exact resolve eq5994 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5994
  have eq6101 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq6048 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6048
  have eq7309 : ∀ X0 X3 X4 : G, (M.op X0 (M.op X3 (M.op X4 X0))) = X0 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq646 x x X0 X0 X4 x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq646
    | exact resolve eq646 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7633 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq270 eq6101
    | exact resolve eq6101 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq6101
  have eq7661 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq7633
  have eq7675 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq7661 eq411
    | exact resolve eq411 eq7661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7733 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq7675
  have eq7764 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq7733 eq688
    | exact resolve eq688 eq7733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq7733
  have eq7800 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq7764 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7764
  have eq7843 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (M.op X0 (M.op X1 (M.op (M.op x y) y))) = (k X0 (M.op X1 (M.op (M.op x y) y))) ∨ (M.op y y) = (k y (M.op X1 (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq255 eq13
    | (have j0 := eq13 X0 y
       have j1 := eq255 X1
       grind)
    | (have r₁ := eq13 y (M.op X0 (M.op (M.op x y) y))
       have r₂ := eq255 X0
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op (M.op x y) y)) y
       have r₂ := eq255 X0
       grind)
    | exact resolve eq13 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq8262 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq7800
    | (have j0 := eq7800 (σ x)
       grind)
    | exact resolve eq7800 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7800
  have eq8328 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106 eq8262
    | exact resolve eq8262 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8262
  have eq8384 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq8328
  have eq10804 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X0) X0)) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (σ (k X3 (τ X0)))) ∨ (σ X3) = (M.op (σ X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq616 X0 (τ X0) X2 X3
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq616
    | exact resolve eq616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq10919 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X0) X0)) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (k (σ X3) X0)) ∨ (σ X3) = (M.op (σ X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10804 X0 X1 X2 X3
       have i₂ := eq38 X0 X3
       grind)
    | exact superpose eq38 eq10804
    | (have j0 := eq10804 X0 X1 X2 X3
       grind)
    | exact resolve eq10804 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq10804
  have eq11754 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (k X0 (M.op X1 (M.op (M.op X2 X0) X0))) ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq737 X0 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq11755 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11754 X0 X1 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq11754
    | (have j0 := eq11754 X0 X1 X2
       grind)
    | exact resolve eq11754 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11754
  have eq12036 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X4 X0) X0)))) = (M.op (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X4 X0) X0)))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq608 X2 X1 X3 x X1
       have i₂ := eq646 x X1 X2 X3 (M.op X1 X2) x
       grind)
    | exact superpose eq646 eq608
    | exact resolve eq608 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq646
  have eq12414 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X4 X0) X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq12036 (M.op (M.op X2 X0) X0) X1 X2 X0 X4
       have i₂ := eq14 X0 (M.op X4 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq12036
    | exact resolve eq12036 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12457 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op X0 (M.op X1 y)) (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq12036
    | exact resolve eq12036 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq12627 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 (M.op (M.op X4 X5) X5)) (M.op (M.op X4 X5) X5)))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X5 (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 (M.op (M.op X4 X5) X5)) (M.op (M.op X4 X5) X5))))) X4
       have i₂ := eq12036 (M.op (M.op X4 X5) X5) X0 X1 X2 X3
       grind)
    | exact superpose eq12036 eq14
    | exact resolve eq14 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12796 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X4 X5) X5)))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq12627 X0 X1 X2 X3 X4 X5
       have i₂ := eq54 X5 X3 X4 (M.op X4 X5)
       grind)
    | exact superpose eq54 eq12627
    | exact resolve eq12627 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq12627
  have eq20611 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7309 x X0 x
       have i₂ := eq2562
       grind)
    | exact superpose eq2562 eq7309
    | exact resolve eq7309 eq2562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562
  have eq21097 : ∀ X0 X1 : G, x = (M.op x (M.op X0 (M.op (M.op X1 y) y))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq617 eq20611
    | exact resolve eq20611 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq20611
  have eq21154 : ∀ X0 X1 : G, x = (M.op x (M.op X0 (M.op X1 y))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq21097 X0 X1
       have i₂ := eq4526 X1
       grind)
    | exact superpose eq4526 eq21097
    | exact resolve eq21097 eq4526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21097
  have eq28049 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12036 y x x X0 x
       have i₂ := eq21154 X0 (M.op x y)
       grind)
    | exact superpose eq21154 eq12036
    | exact resolve eq12036 eq21154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12036 eq21154
  have eq29841 : ∀ X0 X1 : G, y = (M.op y (M.op X1 (M.op X0 x))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq7309 y X1 (M.op X0 x)
       have i₂ := eq28049 X0
       grind)
    | exact superpose eq28049 eq7309
    | exact resolve eq7309 eq28049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32620 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op y y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq7661 eq162
    | exact resolve eq162 eq7661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq7661
  have eq32646 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op y y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq40 eq32620
    | exact resolve eq32620 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq32620
  have eq39815 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op x y) (M.op X2 (M.op X0 (M.op X1 y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5216 X0 X1 X2
       have i₂ := eq4526 X1
       grind)
    | exact superpose eq4526 eq5216
    | exact resolve eq5216 eq4526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4526 eq5216
  have eq60698 : (σ (k x y)) = (k (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq161
       have i₂ := eq32646 x
       grind)
    | exact superpose eq32646 eq161
    | exact resolve eq161 eq32646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq32646
  have eq60850 : (k (σ x) (σ y)) = (k (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq60698
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq60698
    | exact resolve eq60698 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60698
  have eq61041 : (k (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq411 eq60850
    | exact resolve eq60850 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq60850
  have eq61054 : (k (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq61041
  have eq61547 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq8384 eq61054
    | exact resolve eq61054 eq8384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61054
  have eq61586 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq61547
  have eq61593 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq61586
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq61586
    | exact resolve eq61586 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq61586
  have eq61600 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq61593 eq97
    | exact resolve eq97 eq61593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq61593
  have eq61610 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq61600
  have eq61633 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq61610 eq8384
    | exact resolve eq8384 eq61610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8384 eq61610
  have eq61781 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq61633
  have eq61809 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq61781
       have r₂ := eq108
       grind)
    | exact resolve eq61781 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq61781
  have eq61996 : (k (σ y) (M.op (σ x) (σ x))) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq130
       have i₂ := eq61809
       grind)
    | exact superpose eq61809 eq130
    | exact resolve eq130 eq61809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62002 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1619 X0
       have i₂ := eq61809
       grind)
    | exact superpose eq61809 eq1619
    | exact resolve eq1619 eq61809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq62016 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28049 x
       have i₂ := eq61809
       grind)
    | exact superpose eq61809 eq28049
    | exact resolve eq28049 eq61809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28049
  have eq62018 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29841 x x
       have i₂ := eq61809
       grind)
    | exact superpose eq61809 eq29841
    | exact resolve eq29841 eq61809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29841
  have eq62064 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7309 x X0 x
       have i₂ := eq61809
       grind)
    | exact superpose eq61809 eq7309
    | exact resolve eq7309 eq61809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61809
  have eq62077 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq62018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62018
  have eq62079 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq62016
  have eq62113 : ∀ X0 : G, (τ (k X0 (M.op (σ x) (σ x)))) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1602 eq62002
    | exact resolve eq62002 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602 eq62002
  have eq62119 : (k (σ y) (M.op (σ x) (σ x))) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124 eq61996
    | exact resolve eq61996 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq61996
  have eq62437 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op X0 (M.op X1 y)) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq62079 eq12457
    | exact resolve eq12457 eq62079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12457 eq62079
  have eq63538 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq12414 X0 X1 X2 X4
       have i₂ := eq5595 X0 X4
       grind)
    | exact superpose eq5595 eq12414
    | exact resolve eq12414 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12414
  have eq65060 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X4 X5)))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq12796 X0 X1 X2 X3 X4 X5
       have i₂ := eq5595 X5 X4
       grind)
    | exact superpose eq5595 eq12796
    | exact resolve eq12796 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12796
  have eq386106 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 X0))) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11755 X0 X1 X2
       have i₂ := eq5595 X0 X2
       grind)
    | exact superpose eq5595 eq11755
    | (have j0 := eq11755 X0 X1 X2
       grind)
    | exact resolve eq11755 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11755
  have eq386107 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) ∨ (k X0 (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq386106 X0 X1 X2
       have i₂ := eq5595 X0 X2
       grind)
    | exact superpose eq5595 eq386106
    | (have j0 := eq386106 X0 X1 X2
       grind)
    | exact resolve eq386106 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386106
  have eq386665 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (k (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq266 eq386107
    | (have j0 := eq386107 (σ y) X0 (σ x)
       grind)
    | exact resolve eq386107 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq441994 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (k (σ X3) X0)) ∨ (σ X3) = (M.op (σ X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10919 X0 X1 X1 X3
       have i₂ := eq5595 X0 X1
       grind)
    | exact superpose eq5595 eq10919
    | (have j0 := eq10919 X0 X1 X2 X3
       grind)
    | exact resolve eq10919 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595 eq10919
  have eq552769 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (σ x))) ∨ (σ y) = (k (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106 eq386665
    | exact resolve eq386665 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq386665
  have eq552838 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (σ x))) ∨ (σ y) = (k (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq552769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552769
  have eq570536 : (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq552838 eq62119
    | (have j1 := eq552838 (σ x)
       grind)
    | exact resolve eq62119 eq552838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62119 eq552838
  have eq570628 : (σ y) = (k (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by grind
  clear eq570536
  have eq572113 : (τ (σ y)) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq570628 eq62113
    | exact resolve eq62113 eq570628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62113 eq570628
  have eq572201 : (τ (σ y)) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by grind
  clear eq572113
  have eq572249 : (τ (σ y)) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq158 eq572201
    | exact resolve eq572201 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572201
  have eq572257 : (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq29 eq572249
    | exact resolve eq572249 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq572249
  have eq572262 : (k y (M.op x y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq572257 eq158
    | exact resolve eq158 eq572257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq572257
  have eq572296 : (M.op y y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq164 eq572262
    | exact resolve eq572262 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq572262
  have eq572301 : (M.op y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq572296
       have i₂ := eq75 y sF0
       grind)
    | exact superpose eq75 eq572296
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq572296 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572296
  have eq572350 : (M.op y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq572301
  have eq573815 : y = (M.op y (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq572350 eq62077
    | exact resolve eq62077 eq572350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62077 eq572350
  have eq573888 : y = (M.op y (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq573815
  have eq575314 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq62437 y y
       have i₂ := eq573888
       grind)
    | exact superpose eq573888 eq62437
    | exact resolve eq62437 eq573888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62437 eq573888
  have eq575401 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq575314
  have eq575446 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq575401 eq62064
    | exact resolve eq62064 eq575401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62064 eq575401
  have eq575520 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq575446
  have eq575541 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq575520
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq575520
    | exact resolve eq575520 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575520
  have eq575542 : x = (M.op x y) := by grind
  clear eq575541
  have eq575552 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq575542 eq20
    | exact resolve eq20 eq575542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq575557 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq575542 eq109
    | (have r₁ := eq109
       have r₂ := eq575542
       grind)
    | exact resolve eq109 eq575542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq575761 : ∀ X0 X1 X2 : G, x = (M.op x (M.op X0 (M.op X1 (M.op X2 y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq575542 eq39815
    | exact resolve eq39815 eq575542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39815
  have eq575773 : (k x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq575557
  have eq575940 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq575552
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq575552
    | exact resolve eq575552 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575552
  have eq575996 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq575940 eq26
    | exact resolve eq26 eq575940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq576008 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq575940 eq82
    | exact resolve eq82 eq575940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq576840 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq575996 eq7309
    | (have j0 := eq7309 (σ y) X0 (σ x)
       grind)
    | exact resolve eq7309 eq575996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576846 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op X0 (M.op X1 (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq575996 eq63538
    | (have j0 := eq63538 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq63538 eq575996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63538
  have eq582046 : ∀ X1 : G, (σ y) = (M.op (σ y) (k (σ X1) (M.op (σ x) (σ y)))) ∨ (σ X1) = (M.op (σ X1) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq576840 eq441994
    | (have j0 := eq441994 (k (σ X1) (M.op (σ x) (σ y))) X1 x y
       grind)
    | exact resolve eq441994 eq576840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441994 eq576840
  have eq583620 : ∀ X0 : G, y = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq65060 X0 x x x x y
       have i₂ := eq575761 x x x
       grind)
    | exact superpose eq575761 eq65060
    | exact resolve eq65060 eq575761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65060 eq575761
  have eq583913 : (k x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq386107 x y x
       have i₂ := eq583620 x
       grind)
    | exact superpose eq583620 eq386107
    | exact resolve eq386107 eq583620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386107
  have eq604284 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq575773
       grind)
    | exact superpose eq575773 eq44
    | exact resolve eq44 eq575773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575773
  have eq604362 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq604284
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq604284
    | exact resolve eq604284 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604284
  have eq604397 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq575940 eq604362
    | exact resolve eq604362 eq575940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604362
  have eq604945 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq604397 eq75
    | (have j0 := eq75 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq75 eq604397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq604397
  have eq604957 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq575996 eq604945
    | exact resolve eq604945 eq575996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604945
  have eq604966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq575996 eq604957
    | exact resolve eq604957 eq575996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604957
  have eq604973 : (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq604966
       have r₂ := eq27
       grind)
    | exact resolve eq604966 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604966
  have eq605122 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq7309 y X0 y
       have i₂ := eq604973
       grind)
    | exact superpose eq604973 eq7309
    | exact resolve eq7309 eq604973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604973
  have eq610343 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq605122 y
       have i₂ := eq583620 x
       grind)
    | exact superpose eq583620 eq605122
    | exact resolve eq605122 eq583620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605122
  have eq648411 : (σ (k x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq576008 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq576008
    | (have j0 := eq576008 y
       grind)
    | exact resolve eq576008 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576008
  have eq648529 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq575996 eq648411
    | exact resolve eq648411 eq575996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648411
  have eq648797 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq648529
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq648529
    | exact resolve eq648529 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq648529
  have eq648978 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq575940 eq648797
    | exact resolve eq648797 eq575940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648797
  have eq649052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq575996 eq648978
    | exact resolve eq648978 eq575996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648978
  have eq649089 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq649052
       have r₂ := eq27
       grind)
    | exact resolve eq649052 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649052
  have eq649163 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq649089 eq191
    | exact resolve eq191 eq649089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq649089
  have eq649222 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq575542 eq649163
    | exact resolve eq649163 eq575542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649163
  have eq649251 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq583913
       have i₂ := eq649222
       grind)
    | exact superpose eq649222 eq583913
    | exact resolve eq583913 eq649222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583913 eq649222
  have eq649433 : (M.op (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq649251
       grind)
    | exact superpose eq649251 eq70
    | exact resolve eq70 eq649251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649251
  have eq649934 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq649433
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq649433
    | exact resolve eq649433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649433
  have eq649976 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq575940 eq649934
    | exact resolve eq649934 eq575940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649934
  have eq650194 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq649976 eq7309
    | exact resolve eq7309 eq649976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649976
  have eq650487 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (k X0 (M.op X1 (M.op x y))) ∨ (M.op X0 X0) ≠ (M.op y y) ∨ (M.op y y) = (k y (M.op X1 (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq575542 eq7843
    | (have j0 := eq7843 X0 X1
       grind)
    | exact resolve eq7843 eq575542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7843
  have eq650488 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (k X0 (M.op X1 (M.op x y))) ∨ (M.op X0 X0) ≠ (M.op y y) ∨ (M.op y y) = (k y (M.op X1 (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq650487 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq650487
    | (have j0 := eq650487 X0 X1
       grind)
    | exact resolve eq650487 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650487
  have eq650489 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (k X0 (M.op X1 x)) ∨ (M.op X0 X0) ≠ (M.op y y) ∨ (M.op y y) = (k y (M.op X1 (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq575542 eq650488
    | (have j0 := eq650488 X0 X1
       grind)
    | exact resolve eq650488 eq575542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650488
  have eq650490 : ∀ X0 X1 : G, (M.op y y) = (k y (M.op X1 (M.op x y))) ∨ (M.op X0 (M.op X1 x)) = (k X0 (M.op X1 x)) ∨ (M.op X0 X0) ≠ (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq575542 eq650489
    | (have j0 := eq650489 X0 X1
       grind)
    | exact resolve eq650489 eq575542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650489
  have eq650491 : ∀ X0 X1 : G, (M.op y y) = (k y (M.op X1 (M.op x y))) ∨ (M.op X0 (M.op X1 x)) = (k X0 (M.op X1 x)) ∨ (M.op X0 X0) ≠ (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq650490 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq650490
    | (have j0 := eq650490 X0 X1
       grind)
    | exact resolve eq650490 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq650490
  have eq650492 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (M.op X0 (M.op X1 x)) = (k X0 (M.op X1 x)) ∨ (M.op y y) = (k y (M.op X1 x)) := by
    intro X0 X1
    first
    | exact superpose eq575542 eq650491
    | (have j0 := eq650491 X0 X1
       grind)
    | exact resolve eq650491 eq575542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575542 eq650491
  have eq650861 : ∀ X0 : G, (M.op y (M.op X0 x)) = (k y (M.op X0 x)) ∨ (M.op y y) = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have j0 := eq650492 y X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650492
  have eq650867 : ∀ X0 : G, (M.op y y) = (k y (M.op X0 x)) ∨ y = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq650861 X0
       have i₂ := eq583620 X0
       grind)
    | exact superpose eq583620 eq650861
    | (have j0 := eq650861 X0
       grind)
    | exact resolve eq650861 eq583620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583620 eq650861
  have eq658241 : ∀ X0 : G, (σ y) = (M.op (σ y) (k X0 (M.op (σ x) (σ y)))) ∨ (M.op X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq582046 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq582046
    | exact resolve eq582046 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582046
  have eq742036 : (k (σ y) (M.op (σ x) (σ x))) = (σ (M.op y y)) ∨ y = (k y (M.op x x)) := by
    first
    | (have i₁ := eq130
       have i₂ := eq650867 x
       grind)
    | exact superpose eq650867 eq130
    | (have j1 := eq650867 x
       grind)
    | exact resolve eq130 eq650867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq742094 : ∀ X0 : G, y ≠ (M.op y y) ∨ y = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have j0 := eq650867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650867
  have eq742112 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ x))) ∨ y = (k y (M.op x x)) := by
    first
    | (have i₁ := eq742036
       have i₂ := eq129
       grind)
    | exact superpose eq129 eq742036
    | exact resolve eq742036 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq742036
  have eq742138 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (k y (M.op x x)) := by
    first
    | exact superpose eq575940 eq742112
    | exact resolve eq742112 eq575940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742112
  have eq744872 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (k y (M.op x x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq610343 eq742138
    | exact resolve eq742138 eq610343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610343 eq742138
  have eq744911 : y = (k y (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq742094 x
       grind)
    | (have r₁ := eq744872
       have r₂ := eq742094 x
       grind)
    | exact resolve eq744872 eq742094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742094 eq744872
  have eq744978 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x x))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq483 y (M.op x x)
       have i₂ := eq744911
       grind)
    | exact superpose eq744911 eq483
    | (have j0 := eq483 y (M.op x x)
       grind)
    | exact resolve eq483 eq744911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq744911
  have eq744993 : (σ y) = (M.op (σ y) (σ (M.op x x))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq744978
  have eq745004 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq744993
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq744993
    | exact resolve eq744993 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq744993
  have eq745032 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq575940 eq745004
    | exact resolve eq745004 eq575940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745004
  have eq745049 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq745032
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq745032
    | exact resolve eq745032 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq745032
  have eq745186 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq745049 eq7309
    | exact resolve eq7309 eq745049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7309 eq745049
  have eq745276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq575996 eq745186
    | exact resolve eq745186 eq575996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745186
  have eq745288 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq745276
       have r₂ := eq27
       grind)
    | exact resolve eq745276 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745276
  have eq745298 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq745288 eq658241
    | (have j0 := eq658241 (σ y)
       grind)
    | exact resolve eq658241 eq745288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658241 eq745288
  have eq745539 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq745298 eq576846
    | exact resolve eq576846 eq745298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576846 eq745298
  have eq745646 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq745539
  have eq746289 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq745646 eq650194
    | exact resolve eq650194 eq745646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650194 eq745646
  have eq746375 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq575996 eq746289
    | exact resolve eq746289 eq575996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575996 eq746289
  have eq746391 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq746375
       have r₂ := eq27
       grind)
    | exact resolve eq746375 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746375
  have eq746428 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq746391 eq15
    | exact resolve eq15 eq746391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746391
  have eq747100 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq746428
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq746428
    | exact resolve eq746428 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq746428
  have eq747161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq575940 eq747100
    | exact resolve eq747100 eq575940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575940 eq747100
  have eq747187 : False := by grind
  exact eq747187
