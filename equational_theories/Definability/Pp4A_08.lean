import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pxx_pxy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq66 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
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
  clear eq74
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
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
    | (have r₁ := eq110 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq111 (σ X0)
       grind)
    | exact superpose eq111 eq10
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq75
    | exact resolve eq75 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq116 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq49
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq117 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq116
    | exact resolve eq116 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq115
    | exact resolve eq115 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq113
    | exact resolve eq113 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq127 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq101
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq101
    | exact resolve eq101 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq127
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq127
    | exact resolve eq127 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq127
  have eq859 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq120
  have eq990 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq859 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq10904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq10905 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10904
    | exact resolve eq10904 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10904
  have eq10916 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10905
       have r₂ := eq27
       grind)
    | exact resolve eq10905 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10905
  have eq10920 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10916
    | exact resolve eq10916 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10916
  have eq10922 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10920
    | exact resolve eq10920 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10920
  have eq10939 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10922 eq14
    | exact resolve eq14 eq10922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10922
  have eq10960 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51 eq10939
    | exact resolve eq10939 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10939
  have eq10978 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq10960
       grind)
    | exact superpose eq10960 eq14
    | exact resolve eq14 eq10960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10960
  have eq10999 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50 eq10978
    | exact resolve eq10978 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10978
  have eq11015 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10999 eq66
    | (have r₁ := eq66
       have r₂ := eq10999
       grind)
    | exact resolve eq66 eq10999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq10999
  have eq11024 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq11015
  have eq11391 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11024 eq92
    | exact resolve eq92 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq11024
  have eq11412 : (k y x) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128 eq11391
    | exact resolve eq11391 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq11391
  have eq11415 : (k y x) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11412
       have r₂ := eq65
       grind)
    | exact resolve eq11412 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11412
  have eq11426 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq11415
       grind)
    | exact superpose eq11415 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq11415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11415
  have eq11427 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11426
  have eq11429 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11427
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11427
    | exact resolve eq11427 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11427
  have eq11439 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11429
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11429
    | exact resolve eq11429 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11429
  have eq11561 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq11439
       grind)
    | exact superpose eq11439 eq14
    | exact resolve eq14 eq11439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11439
  have eq11584 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq50 eq11561
    | exact resolve eq11561 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq11561
  have eq11585 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq11584
  have eq11598 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq11585 eq29
    | exact resolve eq29 eq11585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11585
  have eq11717 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq11598
    | exact resolve eq11598 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11598
  have eq11718 : y = (M.op x y) ∨ x = y := by grind
  clear eq11717
  have eq11733 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq11718 eq20
    | exact resolve eq20 eq11718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11738 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq11718 eq65
    | (have r₁ := eq65
       have r₂ := eq11718
       grind)
    | exact resolve eq65 eq11718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq11718
  have eq11795 : (k y x) = (M.op y y) ∨ x = y := by grind
  clear eq11738
  have eq11846 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11733
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11733
    | exact resolve eq11733 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11733
  have eq12967 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq990 x y
       have i₂ := eq11795
       grind)
    | exact superpose eq11795 eq990
    | (have j0 := eq990 x y
       grind)
    | exact resolve eq990 eq11795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990 eq11795
  have eq13044 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq12967
  have eq13097 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13044
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq13044
    | exact resolve eq13044 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq13044
  have eq13159 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13097
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13097
    | exact resolve eq13097 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13097
  have eq13220 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13159
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13159
    | exact resolve eq13159 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13159
  have eq13271 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq13220
    | exact resolve eq13220 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13220
  have eq13321 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13271
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13271
    | exact resolve eq13271 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13271
  have eq13367 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13321
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13321
    | exact resolve eq13321 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13321
  have eq13374 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq13367
    | exact resolve eq13367 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13367
  have eq14261 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13374 eq14
    | exact resolve eq14 eq13374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13374
  have eq14288 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq51 eq14261
    | exact resolve eq14261 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq14261
  have eq15362 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14288 eq27
    | exact resolve eq27 eq14288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14288
  have eq15377 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq15362
       have r₂ := eq11846
       grind)
    | exact resolve eq15362 eq11846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11846 eq15362
  have eq15380 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq15377 eq29
    | exact resolve eq29 eq15377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15377
  have eq15527 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq15380
    | exact resolve eq15380 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15380
  have eq15528 : x = y := by grind
  clear eq15527
  have eq15543 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15528
       grind)
    | exact superpose eq15528 eq18
    | exact resolve eq18 eq15528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq15544 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq15528
       grind)
    | exact superpose eq15528 eq24
    | exact resolve eq24 eq15528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15528
  have eq15666 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15544
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15544
    | exact resolve eq15544 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15544
  have eq16864 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15666 eq26
    | exact resolve eq26 eq15666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15666
  have eq17088 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq16864 eq117
    | exact resolve eq117 eq16864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq16864
  have eq17133 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17088
       have i₂ := eq15543
       grind)
    | exact superpose eq15543 eq17088
    | exact resolve eq17088 eq15543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15543 eq17088
  have eq17512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17133 eq15
    | exact resolve eq15 eq17133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17133
  have eq17556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17512
    | exact resolve eq17512 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq17512
  have eq17565 : False := by grind
  exact eq17565

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pyy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq44 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq44 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ X0) (σ X1)
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq85 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq85
    | exact resolve eq85 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq85
  have eq97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq180 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq198 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq9
    | exact resolve eq9 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq97 y
       grind)
    | exact superpose eq97 eq180
    | exact resolve eq180 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq724 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq676
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq676
    | (have j1 := eq58 y x
       grind)
    | exact resolve eq676 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq676
  have eq725 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq724
  have eq4637 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (M.op (σ y) X0) X0)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq725
       grind)
    | exact superpose eq725 eq9
    | exact resolve eq9 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq4666 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4637 x
       have i₂ := eq198 y x
       grind)
    | exact superpose eq198 eq4637
    | exact resolve eq4637 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq4637
  have eq4774 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4666
       grind)
    | exact superpose eq4666 eq10
    | exact resolve eq10 eq4666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666
  have eq4822 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4774
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4774
    | exact resolve eq4774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4774
  have eq4826 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4822
       grind)
    | exact superpose eq4822 eq16
    | exact resolve eq16 eq4822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4822
  have eq4827 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq4826
       have r₂ := eq97 x
       grind)
    | exact resolve eq4826 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4826
  have eq4991 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq4827
       grind)
    | exact superpose eq4827 eq9
    | exact resolve eq9 eq4827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4827
  have eq5026 : x = y := by
    first
    | (have i₁ := eq4991 x
       have i₂ := eq9 x y x
       grind)
    | exact superpose eq9 eq4991
    | exact resolve eq4991 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4991
  have eq5176 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5026
       grind)
    | exact superpose eq5026 eq16
    | exact resolve eq16 eq5026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5026
  have eq5178 : False := by grind
  exact eq5178

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X0)) = X0 := by
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
  have eq56 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 y) y)) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
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
  have eq810 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq6880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq6881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq6880
    | exact resolve eq6880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6880
  have eq6892 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq6881
       have r₂ := eq27
       grind)
    | exact resolve eq6881 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6881
  have eq6894 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq6892
    | exact resolve eq6892 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6892
  have eq6897 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6894 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq6894
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6894
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6894
       grind)
    | exact resolve eq13 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6894
  have eq6905 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq6897
  have eq7463 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6905 eq55
    | exact resolve eq55 eq6905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq6905
  have eq7486 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq7463
    | exact resolve eq7463 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq7463
  have eq7489 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq7486
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq7486
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq7486
       have r₂ := eq13 x y
       grind)
    | exact resolve eq7486 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7486
  have eq7498 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq810 x y
       have i₂ := eq7489
       grind)
    | exact superpose eq7489 eq810
    | (have j0 := eq810 x y
       grind)
    | exact resolve eq810 eq7489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7500 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq7489
       grind)
    | exact superpose eq7489 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq7489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7489
  have eq7501 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7500
  have eq7503 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7498
  have eq7505 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7501
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7501
    | exact resolve eq7501 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7501
  have eq7506 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7505
  have eq7508 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7503
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7503
    | exact resolve eq7503 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7503
  have eq7519 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7508
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7508
    | exact resolve eq7508 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7508
  have eq7521 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7519
    | exact resolve eq7519 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7519
  have eq7522 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7521
  have eq7524 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7522
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7522
    | exact resolve eq7522 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7522
  have eq7526 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7524
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7524
    | exact resolve eq7524 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7524
  have eq8088 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7506
       grind)
    | exact superpose eq7506 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq7506
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7506
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7506
       grind)
    | exact resolve eq12 eq7506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7506
  have eq8098 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8088
  have eq8099 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8098
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8098
    | exact resolve eq8098 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8098
  have eq8100 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8099
  have eq8101 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8100
    | exact resolve eq8100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8100
  have eq8138 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7526 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7526
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7526
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7526
       grind)
    | exact resolve eq12 eq7526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7526
  have eq8148 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8138
  have eq8149 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8148
    | exact resolve eq8148 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8148
  have eq8150 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8149
  have eq8151 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8150
    | exact resolve eq8150 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8150
  have eq8153 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq8101
       grind)
    | exact superpose eq8101 eq91
    | exact resolve eq91 eq8101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8101
  have eq8173 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8153
    | exact resolve eq8153 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8153
  have eq8211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8173 eq8151
    | exact resolve eq8151 eq8173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8151 eq8173
  have eq8216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8211
  have eq8218 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8216
       have r₂ := eq27
       grind)
    | exact resolve eq8216 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8216
  have eq8228 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8218 eq51
    | (have r₁ := eq51
       have r₂ := eq8218
       grind)
    | exact resolve eq51 eq8218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq8218
  have eq8242 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8228
  have eq8257 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8242 eq101
    | exact resolve eq101 eq8242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq8242
  have eq8286 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8257
    | exact resolve eq8257 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8257
  have eq8288 : y = (k y x) := by
    first
    | (have r₁ := eq8286
       have r₂ := eq50
       grind)
    | exact resolve eq8286 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq8286
  have eq8291 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq8288
       grind)
    | exact superpose eq8288 eq91
    | exact resolve eq91 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8300 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq810 y x
       have i₂ := eq8288
       grind)
    | exact superpose eq8288 eq810
    | (have j0 := eq810 y x
       grind)
    | exact resolve eq810 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq8302 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq8288
       grind)
    | exact superpose eq8288 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8303 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq8302
  have eq8305 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8300
  have eq8308 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8303
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8303
    | exact resolve eq8303 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8303
  have eq8310 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8305
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8305
    | exact resolve eq8305 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8305
  have eq8318 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8291
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8291
    | exact resolve eq8291 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8291
  have eq8321 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8310
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8310
    | exact resolve eq8310 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8310
  have eq8324 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8321
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8321
    | exact resolve eq8321 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8321
  have eq8327 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8324
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8324
    | exact resolve eq8324 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8324
  have eq8330 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8327
    | exact resolve eq8327 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8327
  have eq8456 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq8308
       grind)
    | exact superpose eq8308 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8308
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8308
       grind)
    | exact resolve eq12 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8458 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 x) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq8308
       grind)
    | exact superpose eq8308 eq14
    | exact resolve eq14 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8467 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq8456
  have eq8468 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8467
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8467
    | exact resolve eq8467 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8467
  have eq8469 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq8468
  have eq8470 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8469
       have i₂ := eq8288
       grind)
    | exact superpose eq8288 eq8469
    | exact resolve eq8469 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8288 eq8469
  have eq8471 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8470
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8470
    | exact resolve eq8470 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8470
  have eq8537 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq20160 : x = (M.op y (M.op y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8458 y
       have i₂ := eq8308
       grind)
    | exact superpose eq8308 eq8458
    | exact resolve eq8458 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8458
  have eq20186 : x = (M.op y (M.op y x)) ∨ x = (M.op x y) := by grind
  clear eq20160
  have eq20187 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20186
       have i₂ := eq8308
       grind)
    | exact superpose eq8308 eq20186
    | exact resolve eq20186 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8308 eq20186
  have eq20209 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq20187
  have eq20351 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq20209
       grind)
    | exact superpose eq20209 eq56
    | exact resolve eq56 eq20209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq20386 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20351
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20351
    | exact resolve eq20351 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20351
  have eq20400 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8471 eq20386
    | exact resolve eq20386 eq8471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8471 eq20386
  have eq20423 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20400
       have r₂ := eq8537
       grind)
    | exact resolve eq20400 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20400
  have eq20698 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20209
       have i₂ := eq20423
       grind)
    | exact superpose eq20423 eq20209
    | exact resolve eq20209 eq20423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20209 eq20423
  have eq20728 : x = y ∨ x = (M.op x y) := by grind
  clear eq20698
  have eq20732 : x = (M.op x y) := by
    first
    | (have r₁ := eq20728
       have r₂ := eq8537
       grind)
    | exact resolve eq20728 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8537 eq20728
  have eq20735 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20732 eq20
    | exact resolve eq20 eq20732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq20742 : (σ (k y x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20732 eq93
    | exact resolve eq93 eq20732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq20732
  have eq20858 : (k (σ y) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq20742
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq20742
    | exact resolve eq20742 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq20742
  have eq20863 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq20735
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20735
    | exact resolve eq20735 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20735
  have eq20881 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq8318 eq20858
    | exact resolve eq20858 eq8318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8318 eq20858
  have eq20895 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20863 eq26
    | exact resolve eq26 eq20863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq20967 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20863 eq8330
    | exact resolve eq8330 eq20863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8330 eq20863
  have eq21002 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq20967
       have r₂ := eq27
       grind)
    | exact resolve eq20967 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20967
  have eq21433 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21002 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq21002
       grind)
    | exact resolve eq12 eq21002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21436 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ y) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21002 eq14
    | exact resolve eq14 eq21002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21453 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq21433
  have eq21467 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq21002 eq21436
    | exact resolve eq21436 eq21002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21436
  have eq21468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20895 eq21453
    | exact resolve eq21453 eq20895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21453
  have eq21481 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq21468
       have r₂ := eq27
       grind)
    | exact resolve eq21468 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21468
  have eq21487 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20895 eq21481
    | exact resolve eq21481 eq20895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21481
  have eq21491 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20881 eq21487
    | exact resolve eq21487 eq20881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20881 eq21487
  have eq21496 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq21491 eq27
    | exact resolve eq27 eq21491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq21876 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21002 eq21467
    | exact resolve eq21467 eq21002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21002 eq21467
  have eq21973 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq21876 eq57
    | exact resolve eq57 eq21876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq22021 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20895 eq21973
    | exact resolve eq21973 eq20895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20895 eq21973
  have eq22042 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21491 eq22021
    | exact resolve eq22021 eq21491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21491 eq22021
  have eq22058 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21876 eq22042
    | exact resolve eq22042 eq21876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21876 eq22042
  have eq22068 : False := by grind
  exact eq22068

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq74 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq236 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq245 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq980 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq245 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq245
    | (have j0 := eq245 (τ X0) (τ X1)
       grind)
    | exact resolve eq245 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq995 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq980 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq980
    | (have j0 := eq980 X0 X1
       grind)
    | exact resolve eq980 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq1001 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq995 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq995
    | (have j0 := eq995 X0 X1
       grind)
    | exact resolve eq995 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1006 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1001 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1001
    | (have j0 := eq1001 X0 X1
       grind)
    | exact resolve eq1001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1010 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1006 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1006
    | (have j0 := eq1006 X0 X1
       grind)
    | exact resolve eq1006 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1013 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1010 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1010
    | (have j0 := eq1010 X0 X1
       grind)
    | exact resolve eq1010 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1014 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1013 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1013
    | (have j0 := eq1013 X0 X1
       grind)
    | exact resolve eq1013 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq4527 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq74 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq74 (σ X1) X1
       grind)
    | (have r₁ := eq13 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq74 (M.op (M.op (σ X1) (σ X1)) X1) X1
       grind)
    | exact resolve eq13 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4566 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq4567 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566
  have eq4569 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4527 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4527
  have eq4570 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4569 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4569
  have eq4572 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4567 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4567
    | (have j0 := eq4567 X0
       grind)
    | exact resolve eq4567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4567
  have eq4612 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq4572 X0
       grind)
    | exact superpose eq4572 eq40
    | (have j1 := eq4572 X0
       grind)
    | exact resolve eq40 eq4572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4572
  have eq4635 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4612 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4612
    | (have j0 := eq4612 X0
       grind)
    | exact resolve eq4612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4612
  have eq4636 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4635 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4635
  have eq4638 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4636 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4636
    | exact resolve eq4636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4666 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4636 X0
       grind)
    | exact superpose eq4636 eq11
    | exact resolve eq11 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4728 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4638 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq4638
    | exact resolve eq4638 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4638
  have eq4875 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4728 X0
       grind)
    | exact superpose eq4728 eq11
    | exact resolve eq11 eq4728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4986 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4875 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4875
    | exact resolve eq4875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4875
  have eq5050 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq4986 (τ X0)
       grind)
    | exact superpose eq4986 eq36
    | exact resolve eq36 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5105 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5050 X0
       have i₂ := eq4728 X0
       grind)
    | exact superpose eq4728 eq5050
    | exact resolve eq5050 eq4728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4728 eq5050
  have eq5645 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5686 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5645 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5645
    | exact resolve eq5645 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5645
  have eq5735 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5686 X0
       have i₂ := eq4986 X0
       grind)
    | exact superpose eq4986 eq5686
    | exact resolve eq5686 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5686
  have eq5758 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5735
  have eq190677 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4570 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4570
    | exact resolve eq4570 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190859 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X1)
       have i₂ := eq4570 (σ X0) X1
       grind)
    | exact superpose eq4570 eq31
    | (have j1 := eq4570 (σ X0) X1
       grind)
    | exact resolve eq31 eq4570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4570
  have eq191062 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq190859 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq190859
    | (have j0 := eq190859 X0 X1
       grind)
    | exact resolve eq190859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190859
  have eq191193 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190677 X0 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq190677
    | (have j0 := eq190677 X0 X1
       grind)
    | exact resolve eq190677 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq190677
  have eq191276 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq191062 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq191062
    | (have j0 := eq191062 X0 X1
       grind)
    | exact resolve eq191062 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191062
  have eq191465 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq191276 X0 X1
       have i₂ := eq4666 X1
       grind)
    | exact superpose eq4666 eq191276
    | (have j0 := eq191276 X0 X1
       grind)
    | exact resolve eq191276 eq4666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191276
  have eq191606 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq191465 X0 X1
       have i₂ := eq4986 X1
       grind)
    | exact superpose eq4986 eq191465
    | (have j0 := eq191465 X0 X1
       grind)
    | exact resolve eq191465 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191465
  have eq191696 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq191606 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq191606
    | (have j0 := eq191606 X0 X1
       grind)
    | exact resolve eq191606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191606
  have eq196456 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq191193 X1 X0
       grind)
    | exact superpose eq191193 eq11
    | (have j1 := eq191193 X1 X0
       grind)
    | exact resolve eq11 eq191193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191193
  have eq196767 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq196456 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq196456
    | (have j0 := eq196456 X0 X1
       grind)
    | exact resolve eq196456 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196456
  have eq197244 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq196767 X0 (τ X1)
       grind)
    | exact superpose eq196767 eq19
    | (have j1 := eq196767 X0 (τ X1)
       grind)
    | exact resolve eq19 eq196767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq196767
  have eq197735 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq197244 X0 X1
       have i₂ := eq5105 X1
       grind)
    | exact superpose eq5105 eq197244
    | (have j0 := eq197244 X0 X1
       grind)
    | exact resolve eq197244 eq5105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5105 eq197244
  have eq226094 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq197735 (τ X0) X1
       grind)
    | exact superpose eq197735 eq18
    | (have j1 := eq197735 (τ X0) X1
       grind)
    | exact resolve eq18 eq197735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq197735
  have eq226265 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226094 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq226094
    | (have j0 := eq226094 X0 X1
       grind)
    | exact resolve eq226094 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226094
  have eq226434 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226265 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq226265
    | (have j0 := eq226265 X0 X1
       grind)
    | exact resolve eq226265 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226265
  have eq226584 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226434 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq226434
    | (have j0 := eq226434 X0 X1
       grind)
    | exact resolve eq226434 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226434
  have eq241044 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k X1 (σ X0)) = X1 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq226584 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq226584
    | (have j0 := eq226584 X1 (σ X0)
       grind)
    | exact resolve eq226584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226584
  have eq241467 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq241044 X0 X1
       have i₂ := eq4636 X0
       grind)
    | exact superpose eq4636 eq241044
    | (have j0 := eq241044 X0 X1
       grind)
    | exact resolve eq241044 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4636 eq241044
  have eq241581 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq241467 X0 X1
       have i₂ := eq4986 X0
       grind)
    | exact superpose eq4986 eq241467
    | (have j0 := eq241467 X0 X1
       grind)
    | exact resolve eq241467 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241467
  have eq248927 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq241581 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq241581
    | (have j0 := eq241581 X1 (σ X0)
       grind)
    | exact resolve eq241581 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241581
  have eq249314 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq248927 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq248927
    | (have j0 := eq248927 X0 X1
       grind)
    | exact resolve eq248927 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248927
  have eq249513 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq249314 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq249314
    | (have j0 := eq249314 X0 X1
       grind)
    | exact resolve eq249314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249314
  have eq250287 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq236
       have i₂ := eq249513 x y
       grind)
    | exact superpose eq249513 eq236
    | (have j1 := eq249513 x y
       grind)
    | (have r₁ := eq236
       have r₂ := eq249513 x y
       grind)
    | exact resolve eq236 eq249513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq249513
  have eq250502 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq250287
  have eq250622 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq245 x y
       grind)
    | (have r₁ := eq250502
       have r₂ := eq245 x y
       grind)
    | exact resolve eq250502 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq250502
  have eq250867 : (σ x) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq250622
       have i₂ := eq4666 y
       grind)
    | exact superpose eq4666 eq250622
    | exact resolve eq250622 eq4666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666 eq250622
  have eq251027 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq250867
       have i₂ := eq4986 y
       grind)
    | exact superpose eq4986 eq250867
    | exact resolve eq250867 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4986 eq250867
  have eq253813 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq251027
       grind)
    | exact superpose eq251027 eq16
    | exact resolve eq16 eq251027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253818 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq191696 x y
       have i₂ := eq251027
       grind)
    | exact superpose eq251027 eq191696
    | (have j0 := eq191696 x y
       grind)
    | exact resolve eq191696 eq251027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191696 eq251027
  have eq253932 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq253818
  have eq253995 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq253932
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq253932
    | exact resolve eq253932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253932
  have eq253996 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq253995
  have eq257359 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1014 x y
       have i₂ := eq253996
       grind)
    | exact superpose eq253996 eq1014
    | (have j0 := eq1014 x y
       grind)
    | (have r₁ := eq1014 x y
       have r₂ := eq253996
       grind)
    | exact resolve eq1014 eq253996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq253996
  have eq257384 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq257359
  have eq257385 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq257384
  have eq259178 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq253813
       have i₂ := eq257385
       grind)
    | exact superpose eq257385 eq253813
    | exact resolve eq253813 eq257385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253813 eq257385
  have eq259179 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq259178
  have eq259180 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq259179
  have eq259204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5758 y
       have i₂ := eq259180
       grind)
    | exact superpose eq259180 eq5758
    | exact resolve eq5758 eq259180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259180
  have eq259429 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq259204
       have r₂ := eq16
       grind)
    | exact resolve eq259204 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259204
  have eq260680 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq259429
       grind)
    | exact superpose eq259429 eq10
    | exact resolve eq10 eq259429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259429
  have eq261019 : x = (M.op y y) := by
    first
    | (have i₁ := eq260680
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq260680
    | exact resolve eq260680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260680
  have eq261299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5758 y
       have i₂ := eq261019
       grind)
    | exact superpose eq261019 eq5758
    | exact resolve eq5758 eq261019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5758 eq261019
  have eq261529 : False := by grind
  exact eq261529

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_pxx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X0)) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    grind
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq25
  have eq70 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 (σ X0)) (σ X0)))) = (τ (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op (M.op X1 (σ X0)) (σ X0))
       have i₂ := eq34 (σ X0) X1
       grind)
    | exact superpose eq34 eq31
    | exact resolve eq31 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq77 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq4429 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 (σ X1)))) = (τ (M.op (σ X1) (M.op X0 (σ X1)))) ∨ (k X1 (τ (M.op X0 (σ X1)))) = (τ (M.op (σ X1) (M.op X0 (σ X1)))) ∨ (σ X1) = (M.op (M.op X0 (σ X1)) (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq77 X0 (M.op X1 (σ X0))
       grind)
    | exact superpose eq77 eq70
    | (have j1 := eq77 X1 (M.op X0 (σ X1))
       grind)
    | exact resolve eq70 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq4440 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4441 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4440
  have eq4442 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 (σ X1)))) = (τ (M.op (σ X1) (M.op X0 (σ X1)))) ∨ (σ X1) = (M.op (M.op X0 (σ X1)) (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4429 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4429
  have eq4445 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4441 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4441
    | (have j0 := eq4441 X0
       grind)
    | exact resolve eq4441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4441
  have eq4479 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq4445 X0
       grind)
    | exact superpose eq4445 eq40
    | (have j1 := eq4445 X0
       grind)
    | exact resolve eq40 eq4445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4445
  have eq4501 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4479 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4479
    | (have j0 := eq4479 X0
       grind)
    | exact resolve eq4479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4479
  have eq4502 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4501 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4501
  have eq4531 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4502 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4502
    | exact resolve eq4502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4557 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4502 X0
       grind)
    | exact superpose eq4502 eq11
    | exact resolve eq11 eq4502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4502
  have eq4618 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4531 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq4531
    | exact resolve eq4531 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4531
  have eq4637 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4618 X0
       grind)
    | exact superpose eq4618 eq11
    | exact resolve eq11 eq4618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4618
  have eq4748 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4637 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4637
    | exact resolve eq4637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4637
  have eq5107 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5143 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5107 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5107
    | exact resolve eq5107 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5107
  have eq5177 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5143 X0
       have i₂ := eq4748 X0
       grind)
    | exact superpose eq4748 eq5143
    | exact resolve eq5143 eq4748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5143
  have eq5193 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5177
  have eq1647919 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4442 X1 X0
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq4442
    | (have j1 := eq77 X1 X0
       grind)
    | exact resolve eq4442 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq4442
  have eq1648529 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1647919 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647919
  have eq1649541 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1648529 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1648529
    | exact resolve eq1648529 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648529
  have eq1650645 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1649541 X0 X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq1649541
    | (have j0 := eq1649541 X0 X1
       grind)
    | exact resolve eq1649541 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1649541
  have eq1652419 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq1650645 X0 X1
       grind)
    | exact superpose eq1650645 eq11
    | (have j1 := eq1650645 X0 X1
       grind)
    | exact resolve eq11 eq1650645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650645
  have eq1652923 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1652419 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq1652419
    | (have j0 := eq1652419 X0 X1
       grind)
    | exact resolve eq1652419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652419
  have eq1655536 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1652923 (σ X0) (σ X1)
       grind)
    | exact superpose eq1652923 eq15
    | (have j1 := eq1652923 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq1652923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1655617 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1652923 (τ X0) X1
       grind)
    | exact superpose eq1652923 eq18
    | (have j1 := eq1652923 (τ X0) X1
       grind)
    | exact resolve eq18 eq1652923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1652923
  have eq1656293 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1655536 X0 X1
       have i₂ := eq4557 X1
       grind)
    | exact superpose eq4557 eq1655536
    | (have j0 := eq1655536 X0 X1
       grind)
    | exact resolve eq1655536 eq4557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557 eq1655536
  have eq1656991 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1656293 X0 X1
       have i₂ := eq4748 X1
       grind)
    | exact superpose eq4748 eq1656293
    | (have j0 := eq1656293 X0 X1
       grind)
    | exact resolve eq1656293 eq4748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4748 eq1656293
  have eq1670393 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1655617 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1655617
    | exact resolve eq1655617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655617
  have eq1672136 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1670393 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1670393
    | (have j0 := eq1670393 X0 X1
       grind)
    | exact resolve eq1670393 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670393
  have eq1698026 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1656991 x y
       grind)
    | exact superpose eq1656991 eq16
    | (have j1 := eq1656991 x y
       grind)
    | exact resolve eq16 eq1656991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656991
  have eq1701747 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1698026
       have i₂ := eq1672136 x y
       grind)
    | exact superpose eq1672136 eq1698026
    | (have j1 := eq1672136 x y
       grind)
    | (have r₁ := eq1698026
       have r₂ := eq1672136 x y
       grind)
    | exact resolve eq1698026 eq1672136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672136 eq1698026
  have eq1701752 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1701747
  have eq1704043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5193 y
       have i₂ := eq1701752
       grind)
    | exact superpose eq1701752 eq5193
    | exact resolve eq5193 eq1701752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701752
  have eq1704561 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1704043
       have r₂ := eq16
       grind)
    | exact resolve eq1704043 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704043
  have eq1704695 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1704561
       grind)
    | exact superpose eq1704561 eq10
    | exact resolve eq10 eq1704561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704561
  have eq1705950 : x = (M.op y y) := by
    first
    | (have i₁ := eq1704695
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1704695
    | exact resolve eq1704695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704695
  have eq1709075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5193 y
       have i₂ := eq1705950
       grind)
    | exact superpose eq1705950 eq5193
    | exact resolve eq5193 eq1705950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5193 eq1705950
  have eq1709640 : False := by grind
  exact eq1709640

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq45 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq174 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq497 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq498 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq497 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq503 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq498 X0 X1
       have j1 := eq174 X0 X1
       grind)
    | (have r₁ := eq498 X0 X1
       have r₂ := eq174 X0 X1
       grind)
    | (have r₁ := eq498 X1 X1
       have r₂ := eq174 X1 X1
       grind)
    | exact resolve eq498 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq498
  have eq844 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq503 (σ X0) (σ X1)
       grind)
    | exact superpose eq503 eq15
    | exact resolve eq15 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 X1
       have i₂ := eq503 X0 X1
       grind)
    | exact superpose eq503 eq844
    | exact resolve eq844 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq844
  have eq851 : False := by grind
  exact eq851

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_y_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
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
  have eq124 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq169 : ∀ X0 : G, (k (k X0 (M.op x y)) (M.op x y)) = (τ (k (k (σ X0) (σ (M.op x y))) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq85
    | exact resolve eq85 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq174 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq16 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq439 : ∀ X0 X1 : G, (k (k X0 (M.op x y)) (τ X1)) = (τ (k (k (σ X0) (σ (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq41 eq366
    | exact resolve eq366 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq540 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op x (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq552 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 X1 X3 x
       have i₂ := eq177 X1 X0 x
       grind)
    | (have i₁ := eq177 X0 X1 X0
       have i₂ := eq177 X0 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 x
       have i₂ := eq177 X1 X0 x
       grind)
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq177 X0 X0 X2
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 x X1
       have i₂ := eq177 (M.op (M.op X0 X1) X0) x X2
       grind)
    | (have i₁ := eq16 X0 (M.op (M.op X0 X2) X0) X2
       have i₂ := eq177 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq541 X0 x
       have i₂ := eq542 X0 x
       grind)
    | exact superpose eq542 eq541
    | exact resolve eq541 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq761 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq560 (M.op X1 X1) X3 X2
       have i₂ := eq552 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq560 (M.op X1 X1) X3 X2
       have i₂ := eq552 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq552 eq560
    | exact resolve eq560 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op (σ x) (M.op X1 X1)) X3)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq761 x X1 X2 X3
       have i₂ := eq542 X1 x
       grind)
    | exact superpose eq542 eq761
    | exact resolve eq761 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq951 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (k (M.op X0 X1) X0)) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq11 (M.op X0 X1) X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op X0 X1) X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq995 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq1003 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1012 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1012 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1029 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq951 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1044 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1029 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq1029 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq1029 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1029 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1058 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X2 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X2) = (k (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X1) X2
       have i₂ := eq552 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq12 (M.op X1 X1) X2
       have i₂ := eq552 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq552 eq12
    | (have j0 := eq12 (M.op X1 X1) X2
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op (M.op x x) (M.op X0 X0))
       have r₂ := eq552 X0 (M.op X0 X0) x
       grind)
    | (have r₁ := eq12 (M.op x x) (M.op (M.op X0 X0) (M.op x x))
       have r₂ := eq552 X0 (M.op x x) x
       grind)
    | exact resolve eq12 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq1059 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1061 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1059 X0
       have i₂ := eq542 X0 X0
       grind)
    | exact superpose eq542 eq1059
    | (have j0 := eq1059 X0
       grind)
    | exact resolve eq1059 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1062 : ∀ X1 X2 : G, (M.op (σ x) (M.op X1 X1)) ≠ X2 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X2) = (k (M.op X1 X1) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq1058 x X1 X2
       have i₂ := eq542 X1 x
       grind)
    | exact superpose eq542 eq1058
    | (have j0 := eq1058 x X1 X2
       grind)
    | (have r₁ := eq1058 X1 x (M.op (σ x) (M.op x x))
       have r₂ := eq542 x X1
       grind)
    | exact resolve eq1058 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1065 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1061 X0
       have i₂ := eq542 X0 X0
       grind)
    | exact superpose eq542 eq1061
    | (have j0 := eq1061 X0
       grind)
    | exact resolve eq1061 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1101 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1013 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1013
    | (have j0 := eq1013 (σ X0)
       grind)
    | exact resolve eq1013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1103 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1044 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1044
    | (have j0 := eq1044 (σ X0) X1
       grind)
    | exact resolve eq1044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1295 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X1 X1) (M.op X2 (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X1
       have i₂ := eq11 X1 X1
       grind)
    | exact superpose eq11 eq176
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1349 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X1 X1) (M.op X2 (M.op X0 X0))) ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op X2 (M.op X0 X0)) ∨ (M.op X2 (M.op X0 X0)) = (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X1 X1) (M.op X2 (M.op X0 X0))
       have i₂ := eq176 X2 X1 X0
       grind)
    | exact superpose eq176 eq11
    | (have j0 := eq11 (M.op X1 X1) (M.op X2 (M.op X0 X0))
       grind)
    | exact resolve eq11 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1354 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X1 X1) (M.op X2 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1295 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1356 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))) ∨ (M.op X0 X0) = (k (M.op X1 X1) (M.op X2 (M.op X0 X0))) ∨ (M.op (σ x) (M.op X1 X1)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1349 X0 X1 X2
       have i₂ := eq542 X1 X1
       grind)
    | exact superpose eq542 eq1349
    | (have j0 := eq1349 X0 X1 X2
       grind)
    | exact resolve eq1349 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq1349
  have eq1374 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq540 X3 X1 x
       have i₂ := eq540 X0 X1 x
       grind)
    | (have i₁ := eq540 X0 X1 X3
       have i₂ := eq540 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq540 eq540
    | exact resolve eq540 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1387 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq540 X0 (M.op X1 X1) X3
       have i₂ := eq540 X0 X1 X1
       grind)
    | (have i₁ := eq540 X0 (M.op X1 X1) X3
       have i₂ := eq540 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq540 eq540
    | exact resolve eq540 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1416 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op X1 X1)
       have i₂ := eq540 X0 X1 X1
       grind)
    | (have i₁ := eq174 (M.op X1 X1)
       have i₂ := eq540 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq540 eq174
    | exact resolve eq174 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1420 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X2 (M.op X1 X1) X3
       have i₂ := eq540 X0 X1 X1
       grind)
    | (have i₁ := eq177 X0 (M.op X1 X1) X2
       have i₂ := eq540 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq540 eq177
    | exact resolve eq177 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1425 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X1 X1)) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq560 (M.op X1 X1) X3 X2
       have i₂ := eq540 X0 X1 X1
       grind)
    | (have i₁ := eq560 (M.op X1 X1) X1 X2
       have i₂ := eq540 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq540 eq560
    | exact resolve eq560 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq560
  have eq1529 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1387 X0 X1 x X3
       have i₂ := eq176 X0 x X1
       grind)
    | exact superpose eq176 eq1387
    | exact resolve eq1387 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq1387
  have eq2507 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq995
       grind)
    | exact superpose eq995 eq40
    | exact resolve eq40 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq2508 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2507
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2507
    | exact resolve eq2507 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq2510 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2508
    | exact resolve eq2508 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508
  have eq3576 : ∀ X0 : G, (M.op (σ x) (k X0 X0)) = (k X0 (k X0 X0)) ∨ (k X0 X0) = (M.op (σ x) (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1065 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq1065
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1065 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3615 : ∀ X0 : G, (M.op X0 X0) ≠ (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1065 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3616 : ∀ X0 : G, (M.op (σ x) (k X0 X0)) = (k X0 (k X0 X0)) ∨ (k X0 X0) = (M.op (σ x) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3576 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3576
  have eq21653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2510 eq1003
    | exact resolve eq1003 eq2510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21661 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq21653
       have r₂ := eq27
       grind)
    | exact resolve eq21653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21653
  have eq21669 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq21661 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq21661
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq21661
       grind)
    | exact resolve eq13 eq21661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21706 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21661 eq1065
    | exact resolve eq1065 eq21661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21661
  have eq21745 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq21669 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21669
  have eq21766 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq21706
    | exact resolve eq21706 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21706
  have eq21779 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq21766
    | exact resolve eq21766 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21766
  have eq21785 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21745 eq21779
    | exact resolve eq21779 eq21745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21779
  have eq21786 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq21785
  have eq21828 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21786 eq1065
    | exact resolve eq1065 eq21786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21786
  have eq21884 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq21828
    | exact resolve eq21828 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21828
  have eq21895 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq21884
    | exact resolve eq21884 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21884
  have eq21896 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq21895
  have eq21901 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2510 eq21896
    | exact resolve eq21896 eq2510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21896
  have eq21902 : y = (M.op y y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq21901
       have r₂ := eq27
       grind)
    | exact resolve eq21901 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21901
  have eq21905 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq21902
       grind)
    | exact superpose eq21902 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq21902
       grind)
    | exact resolve eq13 eq21902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21902
  have eq21981 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq21905 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21905
  have eq22015 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1101 y
       have i₂ := eq21981 y
       grind)
    | exact superpose eq21981 eq1101
    | (have j0 := eq1101 y
       grind)
    | exact resolve eq1101 eq21981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22059 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq21981 y
       grind)
    | exact superpose eq21981 eq36
    | exact resolve eq36 eq21981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21981
  have eq22069 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22015
  have eq22076 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22059
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22059
    | exact resolve eq22059 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22059
  have eq22105 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22069
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22069
    | exact resolve eq22069 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22069
  have eq23416 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22105 eq1065
    | exact resolve eq1065 eq22105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22105
  have eq23483 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23416
    | exact resolve eq23416 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23416
  have eq23498 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23483
    | exact resolve eq23483 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23483
  have eq23499 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq23498
  have eq23506 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22076 eq23499
    | exact resolve eq23499 eq22076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22076 eq23499
  have eq23507 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23506
  have eq23557 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 x x
       have i₂ := eq23507
       grind)
    | exact superpose eq23507 eq1374
    | exact resolve eq1374 eq23507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23559 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op (M.op x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1416 X0 x
       have i₂ := eq23507
       grind)
    | exact superpose eq23507 eq1416
    | exact resolve eq1416 eq23507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq23579 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1529 X0 x x
       have i₂ := eq23507
       grind)
    | exact superpose eq23507 eq1529
    | exact resolve eq1529 eq23507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23933 : ∀ X0 : G, (M.op (σ x) (M.op X0 y)) = (k y (M.op X0 y)) ∨ (M.op X0 y) = (M.op (σ x) (M.op X0 y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1065 y
       have i₂ := eq23557 X0 y
       grind)
    | (have i₁ := eq1065 y
       have i₂ := eq23557 y x
       grind)
    | exact superpose eq23557 eq1065
    | exact resolve eq1065 eq23557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23977 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X3)) X1) = (M.op (M.op X0 y) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1420 X2 X3 X1 y
       have i₂ := eq23557 X0 X1
       grind)
    | (have i₁ := eq1420 X2 X3 X1 y
       have i₂ := eq23557 X1 X0
       grind)
    | exact superpose eq23557 eq1420
    | exact resolve eq1420 eq23557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq24010 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq23557 X0 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq23557 x X0
       grind)
    | exact superpose eq23557 eq18
    | (have j1 := eq23557 X0 x
       grind)
    | exact resolve eq18 eq23557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23557
  have eq24031 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X1) = (M.op (M.op X2 (M.op X3 X3)) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1 X2 X3
    first
    | exact superpose eq24010 eq23977
    | (have j0 := eq23977 x X1 X2 X3
       grind)
    | exact resolve eq23977 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23977
  have eq24069 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ (M.op X0 y) = (M.op (σ x) (M.op X0 y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23579 eq23933
    | (have j0 := eq23933 X0
       grind)
    | exact resolve eq23933 eq23579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23933
  have eq24173 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ y = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23579 eq24069
    | (have j0 := eq24069 X0
       grind)
    | exact resolve eq24069 eq23579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24069
  have eq24206 : ∀ X0 : G, y = (k y (M.op x y)) ∨ y = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24010 eq24173
    | (have j0 := eq24173 x
       grind)
    | exact resolve eq24173 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24173
  have eq24213 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24010 eq24206
    | (have j0 := eq24206 x
       grind)
    | exact resolve eq24206 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24206
  have eq24283 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 y x
       have i₂ := eq24010 y
       grind)
    | exact superpose eq24010 eq1374
    | exact resolve eq1374 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24305 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1529 X0 y x
       have i₂ := eq24010 y
       grind)
    | exact superpose eq24010 eq1529
    | exact resolve eq1529 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24347 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq803 x x y
       have i₂ := eq24010 (M.op sF2 (M.op x x))
       grind)
    | exact superpose eq24010 eq803
    | exact resolve eq803 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq24421 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23579 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23579
    | (have j0 := eq23579 X0 x
       grind)
    | exact resolve eq23579 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24474 : ∀ X0 X1 : G, y ≠ (M.op X0 y) ∨ (M.op X0 y) = (k X1 (M.op X0 y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 y)
       have i₂ := eq23579 (M.op X0 y) X0
       grind)
    | exact superpose eq23579 eq13
    | (have j0 := eq13 X1 (M.op X0 y)
       grind)
    | exact resolve eq13 eq23579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24615 : y = (k y (M.op y y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1065 y
       have i₂ := eq23579 sF2 y
       grind)
    | exact superpose eq23579 eq1065
    | exact resolve eq1065 eq23579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24629 : y = (k y (M.op x y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24010 eq24615
    | exact resolve eq24615 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24615
  have eq24652 : ∀ X0 X1 : G, y ≠ (M.op x y) ∨ (M.op X0 y) = (k X1 (M.op X0 y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq24010 eq24474
    | (have j0 := eq24474 x X1
       grind)
    | exact resolve eq24474 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24474
  have eq24659 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24213 eq24629
    | exact resolve eq24629 eq24213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24629
  have eq24664 : ∀ X1 : G, y ≠ (M.op x y) ∨ (M.op x y) = (k X1 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq24010 eq24652
    | (have j0 := eq24652 x X1
       grind)
    | exact resolve eq24652 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24652
  have eq24731 : (k (M.op x y) y) = (M.op (σ x) y) ∨ y = (M.op (σ x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24421 eq1065
    | exact resolve eq1065 eq24421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24839 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op (σ x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24010 eq24731
    | exact resolve eq24731 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24731
  have eq24846 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24010 eq24839
    | exact resolve eq24839 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24839
  have eq25521 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op x y))) = (k (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op X0 (M.op x y)) = (M.op (σ x) (M.op X0 (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24283 eq1065
    | exact resolve eq1065 eq24283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25681 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op X0 (M.op x y)) = (M.op (σ x) (M.op X0 (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24305 eq25521
    | (have j0 := eq25521 X0
       grind)
    | exact resolve eq25521 eq24305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25521
  have eq25804 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24305 eq25681
    | (have j0 := eq25681 X0
       grind)
    | exact resolve eq25681 eq24305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25681
  have eq25844 : ∀ X0 : G, (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24421 eq25804
    | (have j0 := eq25804 X0
       grind)
    | exact resolve eq25804 eq24421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25804
  have eq27585 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24846 eq40
    | exact resolve eq40 eq24846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24846
  have eq27589 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq27585
    | exact resolve eq27585 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27585
  have eq29286 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X0) (k x (M.op X1 y))) ∨ (M.op x x) = (M.op X1 y) ∨ (M.op X1 y) = (M.op (M.op X1 y) (M.op X1 y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq23559 eq973
    | (have j0 := eq973 (M.op X1 y) X1 x
       grind)
    | exact resolve eq973 eq23559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23559
  have eq29312 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X0) (k x (M.op X1 y))) ∨ y = (M.op X1 y) ∨ (M.op X1 y) = (M.op (M.op X1 y) (M.op X1 y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq23507 eq29286
    | (have j0 := eq29286 X0 X1
       grind)
    | exact resolve eq29286 eq23507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23507 eq29286
  have eq29329 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X0) (k x (M.op X1 y))) ∨ y = (M.op X1 y) ∨ y = (M.op X1 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq23579 eq29312
    | (have j0 := eq29312 X0 X1
       grind)
    | exact resolve eq29312 eq23579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23579 eq29312
  have eq29330 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X0) (k x (M.op X1 y))) ∨ y = (M.op X1 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq29329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29329
  have eq29340 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X0) (k x (M.op x y))) ∨ y = (M.op X1 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq24010 eq29330
    | (have j0 := eq29330 X0 x
       grind)
    | exact resolve eq29330 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29330
  have eq29345 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (k x (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24010 eq29340
    | (have j0 := eq29340 X0 x
       grind)
    | exact resolve eq29340 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24010 eq29340
  have eq33894 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k X0 (M.op x y)) ∨ y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24659 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq24659
       grind)
    | exact resolve eq13 eq24659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24659
  have eq33996 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq33894 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33894
  have eq34375 : y ≠ (M.op x y) ∨ y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33996
  have eq34383 : y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34375
       have r₂ := eq24213
       grind)
    | exact resolve eq34375 eq24213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24213 eq34375
  have eq34427 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34383 eq41
    | exact resolve eq41 eq34383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34383
  have eq34430 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34427
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34427
    | exact resolve eq34427 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34427
  have eq34857 : ∀ X0 : G, (M.op X0 (M.op x y)) ≠ (k (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op X0 (M.op x y)) = (M.op (σ x) (M.op X0 (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24283 eq3615
    | exact resolve eq3615 eq24283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24283
  have eq34922 : ∀ X0 : G, (M.op X0 (M.op x y)) ≠ (k (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24305 eq34857
    | (have j0 := eq34857 X0
       grind)
    | exact resolve eq34857 eq24305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24305 eq34857
  have eq34956 : ∀ X0 : G, y ≠ (k (M.op x y) y) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24421 eq34922
    | (have j0 := eq34922 X0
       grind)
    | exact resolve eq34922 eq24421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34922
  have eq34975 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25844 eq34956
    | (have j0 := eq34956 X0
       have j1 := eq25844 X0
       grind)
    | exact resolve eq34956 eq25844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25844 eq34956
  have eq54631 : (M.op x y) = (M.op (M.op x y) (k x (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29345 eq24031
    | exact resolve eq24031 eq29345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24031 eq29345
  have eq54670 : (M.op x y) = (M.op (M.op x y) (k x (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq54631
  have eq54828 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54670 eq973
    | (have j0 := eq973 (M.op x y) x x
       grind)
    | exact resolve eq973 eq54670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973 eq54670
  have eq54846 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq54828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54828
  have eq54856 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq54846 X0
       have j1 := eq34975 (M.op x y)
       grind)
    | (have r₁ := eq54846 X0
       have r₂ := eq34975 X0
       grind)
    | exact resolve eq54846 eq34975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54846
  have eq54866 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (k (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24421 eq54856
    | (have j0 := eq54856 X0
       grind)
    | exact resolve eq54856 eq24421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24421 eq54856
  have eq55694 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 X0) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq54866 eq1425
    | exact resolve eq1425 eq54866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq55699 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 X0) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq54866 eq1354
    | (have j0 := eq1354 (M.op x y) x x
       grind)
    | exact resolve eq1354 eq54866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354 eq54866
  have eq55794 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 X0) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq55699 X0
       have j1 := eq34975 (M.op x y)
       grind)
    | (have r₁ := eq55699 X0
       have r₂ := eq34975 X0
       grind)
    | exact resolve eq55699 eq34975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34975 eq55699
  have eq55795 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24347 eq55694
    | exact resolve eq55694 eq24347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55694
  have eq55830 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24347 eq55794
    | exact resolve eq55794 eq24347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24347 eq55794
  have eq55843 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55795 eq41
    | exact resolve eq41 eq55795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55879 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq55843
    | exact resolve eq55843 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55843
  have eq55889 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55879
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55879
    | exact resolve eq55879 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55879
  have eq56106 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k X0 (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq55830 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq55830
       grind)
    | exact resolve eq13 eq55830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55830
  have eq56255 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq56106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56106
  have eq58038 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq56255
  have eq58066 : y = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq58038
       have r₂ := eq55795
       grind)
    | exact resolve eq58038 eq55795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55795 eq58038
  have eq63078 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55889 eq3616
    | (have j0 := eq3616 (σ (M.op x y))
       grind)
    | exact resolve eq3616 eq55889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616 eq55889
  have eq63199 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq63078
    | exact resolve eq63078 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63078
  have eq63245 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq63199
    | exact resolve eq63199 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63199
  have eq63246 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq63245
  have eq63272 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27589 eq63246
    | exact resolve eq63246 eq27589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27589 eq63246
  have eq63274 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq63272
       have r₂ := eq27
       grind)
    | exact resolve eq63272 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63272
  have eq63277 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq63274 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq63274
       grind)
    | exact resolve eq13 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63274
  have eq63432 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq63277 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63277
  have eq63597 : ∀ X0 : G, (τ (k (σ (M.op x y)) (σ (M.op x y)))) = (k (k X0 (M.op x y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq63432 eq169
    | exact resolve eq169 eq63432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq63630 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (k X0 (M.op x y)) (τ (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq63432 eq439
    | exact resolve eq439 eq63432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq63647 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63432 eq124
    | exact resolve eq124 eq63432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq63660 : (τ (σ (M.op x y))) = (k y (τ (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63432 eq107
    | exact resolve eq107 eq63432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63432
  have eq63682 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq63660
    | exact resolve eq63660 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63660
  have eq63690 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq63647
    | exact resolve eq63647 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63647
  have eq63703 : ∀ X0 : G, (M.op x y) = (k (k X0 (M.op x y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq63630
    | exact resolve eq63630 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq63630
  have eq63736 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (k (k X0 (M.op x y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq133 eq63597
    | exact resolve eq63597 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq63597
  have eq63750 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq24664 y
       grind)
    | (have r₁ := eq63682
       have r₂ := eq24664 x
       grind)
    | exact resolve eq63682 eq24664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63682
  have eq63758 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq24664 (M.op x y)
       grind)
    | (have r₁ := eq63690
       have r₂ := eq24664 x
       grind)
    | exact resolve eq63690 eq24664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63690
  have eq63763 : ∀ X0 : G, (M.op x y) = (k (k X0 (M.op x y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq63703 X0
       have j1 := eq24664 (k X0 (M.op x y))
       grind)
    | (have r₁ := eq63703 X0
       have r₂ := eq24664 x
       grind)
    | exact resolve eq63703 eq24664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24664 eq63703
  have eq63789 : ∀ X0 : G, y = (k (k X0 (M.op x y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58066 eq63736
    | exact resolve eq63736 eq58066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58066 eq63736
  have eq63800 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63763 eq63789
    | exact resolve eq63789 eq63763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63763 eq63789
  have eq63801 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq63800
  have eq63808 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63801 eq27
    | exact resolve eq27 eq63801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63801
  have eq63838 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63750 eq36
    | exact resolve eq36 eq63750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq63750
  have eq63850 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq63838
    | exact resolve eq63838 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63838
  have eq63854 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34430 eq63850
    | exact resolve eq63850 eq34430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34430 eq63850
  have eq63928 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63758 eq1101
    | (have j0 := eq1101 (M.op x y)
       grind)
    | exact resolve eq1101 eq63758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq63929 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq63758 eq1103
    | (have j0 := eq1103 (M.op x y) X0
       grind)
    | exact resolve eq1103 eq63758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq63758
  have eq63942 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq63929 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63929
  have eq63943 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq63928
  have eq63957 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq63942
    | (have j0 := eq63942 X0
       grind)
    | exact resolve eq63942 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63942
  have eq63958 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq63943
    | exact resolve eq63943 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63943
  have eq63967 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq63854 eq63957
    | exact resolve eq63957 eq63854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63957
  have eq63968 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63854 eq63958
    | exact resolve eq63958 eq63854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63854 eq63958
  have eq64950 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63968 eq3615
    | exact resolve eq3615 eq63968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63968
  have eq65072 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq64950
       have r₂ := eq63967 (σ y)
       grind)
    | exact resolve eq64950 eq63967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63967 eq64950
  have eq65136 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq65072
    | exact resolve eq65072 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65072
  have eq65137 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq65136
  have eq65166 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq65137 eq27
    | exact resolve eq27 eq65137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178500 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21745 eq2510
    | exact resolve eq2510 eq21745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21745
  have eq178532 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq178500
  have eq178558 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq178532
       have r₂ := eq65166
       grind)
    | exact resolve eq178532 eq65166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178532
  have eq178697 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq178558 eq1374
    | exact resolve eq1374 eq178558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178558
  have eq183089 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq178697 eq26
    | (have j1 := eq178697 X0 (σ x)
       grind)
    | exact resolve eq26 eq178697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178697
  have eq183311 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq65137 eq183089
    | exact resolve eq183089 eq65137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183089
  have eq183814 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq183311 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq183311 (σ y)
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq183311 X0
       grind)
    | exact resolve eq13 eq183311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183311
  have eq184327 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq183814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183814
  have eq184605 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq184327 eq2510
    | exact resolve eq2510 eq184327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510
  have eq184626 : (τ (σ y)) = (k y (τ (σ y))) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq184327 eq107
    | exact resolve eq107 eq184327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq184327
  have eq184637 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq184605
  have eq184656 : y = (k y y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq184626
    | exact resolve eq184626 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq184626
  have eq184662 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq184637
       have r₂ := eq65166
       grind)
    | exact resolve eq184637 eq65166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184637
  have eq184708 : y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq184656
       have r₂ := eq13 x y
       grind)
    | exact resolve eq184656 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184656
  have eq184839 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 y x
       have i₂ := eq184662
       grind)
    | exact superpose eq184662 eq1374
    | exact resolve eq1374 eq184662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184866 : y ≠ (k y y) ∨ y = (M.op (σ x) y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3615 y
       have i₂ := eq184662
       grind)
    | exact superpose eq184662 eq3615
    | exact resolve eq3615 eq184662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3615 eq184662
  have eq185054 : y = (M.op (σ x) y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq184866
       have r₂ := eq184708
       grind)
    | exact resolve eq184866 eq184708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184708 eq184866
  have eq187787 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq184839 X0 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq184839 x X0
       grind)
    | exact superpose eq184839 eq18
    | (have j1 := eq184839 X0 x
       grind)
    | exact resolve eq18 eq184839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187840 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq185054
       have i₂ := eq184839 X0 sF2
       grind)
    | (have i₁ := eq185054
       have i₂ := eq184839 sF2 x
       grind)
    | exact superpose eq184839 eq185054
    | exact resolve eq185054 eq184839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184839
  have eq187879 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq187840 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187840
  have eq188957 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq185054
       have i₂ := eq187787 sF2
       grind)
    | exact superpose eq187787 eq185054
    | exact resolve eq185054 eq187787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185054 eq187787
  have eq188996 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq188957
  have eq189233 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 x X1
       have i₂ := eq188996
       grind)
    | exact superpose eq188996 eq177
    | exact resolve eq177 eq188996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq189271 : (k x y) = (M.op (σ x) y) ∨ y = (M.op (σ x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1065 x
       have i₂ := eq188996
       grind)
    | exact superpose eq188996 eq1065
    | exact resolve eq1065 eq188996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq189283 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 x x
       have i₂ := eq188996
       grind)
    | exact superpose eq188996 eq1374
    | exact resolve eq1374 eq188996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189305 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1529 X0 x x
       have i₂ := eq188996
       grind)
    | exact superpose eq188996 eq1529
    | exact resolve eq1529 eq188996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189495 : ∀ X0 : G, (M.op x y) = (M.op (σ x) y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq574 x
       have i₂ := eq187879 X0
       grind)
    | exact superpose eq187879 eq574
    | (have j1 := eq187879 X0
       grind)
    | exact resolve eq574 eq187879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq189553 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op X1 y)) ∨ y = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1529 X0 x x
       have i₂ := eq187879 X0
       grind)
    | exact superpose eq187879 eq1529
    | (have j1 := eq187879 X2
       grind)
    | exact resolve eq1529 eq187879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529 eq187879
  have eq189726 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op X1 y)) ∨ (M.op x y) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq189305 eq189553
    | (have j0 := eq189553 X0 X1 X2
       have j1 := eq189305 X0 X1
       grind)
    | exact resolve eq189553 eq189305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189553
  have eq189778 : ∀ X0 : G, (M.op x y) = (M.op (σ x) y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq189495 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq189495
    | (have j0 := eq189495 X0
       grind)
    | exact resolve eq189495 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189495
  have eq192335 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq189283 X0 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq189283 x X0
       grind)
    | exact superpose eq189283 eq18
    | (have j1 := eq189283 X0 x
       grind)
    | exact resolve eq18 eq189283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192388 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 y) ∨ y = (M.op X1 y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq189778 X0
       have i₂ := eq189283 X0 sF2
       grind)
    | (have i₁ := eq189778 X0
       have i₂ := eq189283 sF2 X1
       grind)
    | exact superpose eq189283 eq189778
    | (have j0 := eq189778 X1
       have j1 := eq189283 X0 x
       grind)
    | exact resolve eq189778 eq189283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189283 eq189778
  have eq193425 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op X0 X1) X0)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1 y
       have i₂ := eq192335 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq192335 eq568
    | exact resolve eq568 eq192335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq193630 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq189233 eq193425
    | exact resolve eq193425 eq189233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189233 eq193425
  have eq193886 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq189305 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq189305
    | (have j0 := eq189305 X0 x
       grind)
    | exact resolve eq189305 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189305
  have eq201875 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y y) = (k (M.op X0 X0) y) ∨ y = (M.op (σ x) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq193630 eq1356
    | exact resolve eq1356 eq193630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356 eq193630
  have eq202407 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y y) = (k (M.op X0 X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq201875 X0
       have j1 := eq1062 X0 y
       grind)
    | (have r₁ := eq201875 x
       have r₂ := eq1062 x y
       grind)
    | exact resolve eq201875 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq201875
  have eq202497 : ∀ X0 : G, y = (M.op y y) ∨ (M.op x y) = (k (M.op X0 X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq192388 eq202407
    | (have j1 := eq192388 X0 y
       grind)
    | exact resolve eq202407 eq192388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192388 eq202407
  have eq202539 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x y) = (k (M.op X0 X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq192335 eq202497
    | (have j0 := eq202497 X0
       grind)
    | exact resolve eq202497 eq192335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192335 eq202497
  have eq202540 : ∀ X0 : G, (M.op x y) = (k (M.op X0 X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq202539 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202539
  have eq205446 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq202540 x
       have i₂ := eq188996
       grind)
    | exact superpose eq188996 eq202540
    | exact resolve eq202540 eq188996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188996 eq202540
  have eq205508 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq205446
  have eq205562 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq205508
       grind)
    | exact superpose eq205508 eq40
    | exact resolve eq40 eq205508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205508
  have eq205679 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq205562
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq205562
    | exact resolve eq205562 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205562
  have eq205698 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq205679
    | exact resolve eq205679 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205679
  have eq225956 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ y = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq189726 X0 x X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq189726
    | (have j0 := eq189726 X0 x X1
       grind)
    | exact resolve eq189726 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189726
  have eq227308 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq225956 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225956
  have eq227317 : ∀ X0 : G, y = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq227308 X0
       have j1 := eq193886 X0
       grind)
    | (have r₁ := eq227308 X0
       have r₂ := eq193886 X0
       grind)
    | exact resolve eq227308 eq193886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193886 eq227308
  have eq227650 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) := by
    intro X0 X1
    first
    | exact superpose eq227317 eq1374
    | exact resolve eq1374 eq227317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227317
  have eq229284 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq227650 X0 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq227650 x X0
       grind)
    | exact superpose eq227650 eq18
    | (have j1 := eq227650 X0 x
       grind)
    | exact resolve eq18 eq227650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq227650
  have eq553842 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq189271
       have i₂ := eq229284 sF2
       grind)
    | exact superpose eq229284 eq189271
    | exact resolve eq189271 eq229284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189271 eq229284
  have eq554061 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq553842
  have eq559325 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq554061
       grind)
    | exact superpose eq554061 eq40
    | exact resolve eq40 eq554061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq554061
  have eq559348 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq559325
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq559325
    | exact resolve eq559325 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq559325
  have eq559353 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq559348
    | exact resolve eq559348 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559348
  have eq559374 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq559353 eq1003
    | exact resolve eq1003 eq559353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003 eq559353
  have eq559414 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq559374
       have r₂ := eq27
       grind)
    | exact resolve eq559374 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq559374
  have eq559732 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq559414 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq559414
       grind)
    | exact resolve eq13 eq559414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559414
  have eq560117 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq559732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559732
  have eq561988 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq560117 eq205698
    | exact resolve eq205698 eq560117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560117
  have eq562003 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq561988
  have eq562056 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq562003
       have r₂ := eq63808
       grind)
    | exact resolve eq562003 eq63808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562003
  have eq562272 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq562056 eq1374
    | exact resolve eq1374 eq562056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374 eq562056
  have eq566259 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq562272 eq26
    | (have j1 := eq562272 X0 (σ x)
       grind)
    | exact resolve eq26 eq562272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq562272
  have eq566613 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq65137 eq566259
    | exact resolve eq566259 eq65137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65137 eq566259
  have eq568204 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq566613 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq566613 (σ y)
       grind)
    | exact resolve eq13 eq566613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566613
  have eq569094 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq568204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568204
  have eq569800 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq569094 eq205698
    | exact resolve eq205698 eq569094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205698 eq569094
  have eq569815 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq569800
  have eq569866 : y = (M.op x y) := by
    first
    | (have r₁ := eq569815
       have r₂ := eq63808
       grind)
    | exact resolve eq569815 eq63808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63808 eq569815
  have eq569996 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq569866
       grind)
    | exact superpose eq569866 eq24
    | exact resolve eq24 eq569866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq569866
  have eq570370 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq569996 eq20
    | exact resolve eq20 eq569996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq569996
  have eq570551 : False := by grind
  exact eq570551

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_y_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op (M.op X0 X2) X0) = (M.op (M.op (M.op X0 X2) X0) (M.op (M.op X0 X2) X0)) ∨ (M.op (M.op (M.op X0 X2) X0) (M.op (M.op X0 X2) X0)) = (k (M.op X1 X1) (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X1) (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 X1) (M.op (M.op X0 X2) X0)
       grind)
    | (have r₁ := eq12 (M.op X1 X1) (M.op (M.op (M.op X1 X1) X2) (M.op X1 X1))
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq138 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq127 eq16
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq152 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq169 : (k (M.op x y) x) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq138
       have i₂ := eq11 sF1 sF2
       grind)
    | exact superpose eq11 eq138
    | (have j1 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq173 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq152
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq152
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq175 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq173
  have eq206 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq328 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (σ (k x (k X0 (τ X1)))) = (k (σ x) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq35
    | exact resolve eq35 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq38
  have eq342 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq62
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 X2)) = (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X1 X2) X3 X1
       have i₂ := eq62 X1 X0 X2
       grind)
    | (have i₁ := eq62 (M.op X1 X1) X1 X0
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq59 eq62
    | exact resolve eq62 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq354 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq60 eq62
    | exact resolve eq62 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq356 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 x X2
       have i₂ := eq62 X0 x X1
       grind)
    | (have i₁ := eq62 X2 X2 X2
       have i₂ := eq62 X2 X1 X2
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq62 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq62 X0 X0 X2
       grind)
    | exact superpose eq62 eq14
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq206 x
       have i₂ := eq62 x x X0
       grind)
    | (have i₁ := eq206 x
       have i₂ := eq62 x x x
       grind)
    | exact superpose eq62 eq206
    | exact resolve eq206 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq209 sF2
       have i₂ := eq62 sF2 x sF2
       grind)
    | (have i₁ := eq209 x
       have i₂ := eq62 sF2 x x
       grind)
    | exact superpose eq62 eq209
    | exact resolve eq209 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq228 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq228
    | exact resolve eq228 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 : G, (k (τ X0) (k y y)) = (τ (k X0 (k (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq228 X0 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq228
    | exact resolve eq228 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq494 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq228 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq228
    | (have j0 := eq228 X0 y
       grind)
    | exact resolve eq228 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq228
    | (have j0 := eq228 X0 (M.op x y)
       grind)
    | exact resolve eq228 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq553 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq72 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq72 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq72 X0 X1
       grind)
    | exact resolve eq13 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq567 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq577 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq553 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq579 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq577 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq577 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq577 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq623 : (k (k y y) y) = (τ (k (k (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq102 eq494
    | exact resolve eq494 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) ∨ (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) = (k (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq112 (M.op X0 X0) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq822 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq353 sF0
       have i₂ := eq62 sF0 x x
       grind)
    | exact superpose eq62 eq353
    | exact resolve eq353 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq354 sF4
       have i₂ := eq62 sF4 x sF2
       grind)
    | exact superpose eq62 eq354
    | exact resolve eq354 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq354 eq62
    | exact resolve eq62 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) X1) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq354 eq356
    | exact resolve eq356 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq357 X0 X1 (M.op (M.op X0 X0) X1)
       have i₂ := eq356 (M.op (M.op X0 X0) X1) X2 (M.op (M.op X0 X0) X1)
       grind)
    | (have i₁ := eq357 X0 X1 (M.op (M.op X0 X0) X1)
       have i₂ := eq356 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1) X2
       grind)
    | exact superpose eq356 eq357
    | exact resolve eq357 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X0) (M.op x y))) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq822 eq62
    | exact resolve eq62 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq1037 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1033 X0 x
       have i₂ := eq357 X0 sF0 x
       grind)
    | exact superpose eq357 eq1033
    | exact resolve eq1033 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1074 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq342 X3 X1 x
       have i₂ := eq342 X0 X1 x
       grind)
    | (have i₁ := eq342 X0 X1 X3
       have i₂ := eq342 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq342 eq342
    | exact resolve eq342 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq342 X0 (M.op X1 X1) X3
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq342 X0 (M.op X1 X1) X3
       have i₂ := eq342 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq342 eq342
    | exact resolve eq342 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1112 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X1) X2
       have i₂ := eq342 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq342 eq14
    | exact resolve eq14 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1119 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq206 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq206 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq206
    | exact resolve eq206 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X2) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq357 X2 X3 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq357 X0 X1 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1037 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq1037 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq1037
    | exact resolve eq1037 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq1037
  have eq1170 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1085 X0 X1 x X3
       have i₂ := eq61 X0 x X1
       grind)
    | exact superpose eq61 eq1085
    | exact resolve eq1085 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1085
  have eq1187 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq835 eq62
    | exact resolve eq62 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq1191 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1187 X0 x
       have i₂ := eq357 X0 sF4 x
       grind)
    | exact superpose eq357 eq1187
    | exact resolve eq1187 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1199 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1191 sF4
       have i₂ := eq356 sF4 x sF4
       grind)
    | (have i₁ := eq1191 sF4
       have i₂ := eq356 sF4 sF4 x
       grind)
    | exact superpose eq356 eq1191
    | exact resolve eq1191 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq1191
  have eq1945 : ∀ X0 X1 : G, (k x (k X0 (τ X1))) = (τ (k (σ x) (k (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k x (k X0 (τ X1)))
       have i₂ := eq329 X0 X1
       grind)
    | exact superpose eq329 eq16
    | exact resolve eq16 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq2291 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq579 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq579
    | (have j0 := eq579 (τ X0) X1
       grind)
    | exact resolve eq579 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq2299 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2291 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2291
    | (have j0 := eq2291 X0 X1
       grind)
    | exact resolve eq2291 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291
  have eq2305 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2299 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2299
    | (have j0 := eq2299 X0 X1
       grind)
    | exact resolve eq2299 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299
  have eq2409 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2305 (τ X0) X1
       have i₂ := eq478 X0 X0
       grind)
    | exact superpose eq478 eq2305
    | (have j0 := eq2305 (τ X0) X1
       grind)
    | exact resolve eq2305 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305
  have eq3227 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq567 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq567
    | (have j0 := eq567 (τ X0)
       grind)
    | exact resolve eq567 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3235 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3227 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3227
    | (have j0 := eq3227 X0
       grind)
    | exact resolve eq3227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq3241 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3235 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3235
    | (have j0 := eq3235 X0
       grind)
    | exact resolve eq3235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3235
  have eq3350 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) x) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op x y) x) X1)) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq353 eq345
    | exact resolve eq345 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq3351 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq354 eq345
    | exact resolve eq345 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq354
  have eq3567 : ∀ X1 X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ x)) := by
    intro X1 X2
    first
    | exact superpose eq209 eq3351
    | exact resolve eq3351 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq3351
  have eq3568 : ∀ X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op x y) x) X1)) x) := by
    intro X1 X2
    first
    | (have i₁ := eq3350 x X1 X2
       have i₂ := eq206 x
       grind)
    | exact superpose eq206 eq3350
    | exact resolve eq3350 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq3350
  have eq3596 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3241 (τ X0)
       have i₂ := eq478 X0 X0
       grind)
    | exact superpose eq478 eq3241
    | (have j0 := eq3241 (τ X0)
       grind)
    | exact resolve eq3241 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq5744 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq74 eq12
    | (have j0 := eq12 (σ y) (σ X0)
       have j1 := eq74 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ X0)
       have r₂ := eq74 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq74 X0
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq5755 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5744 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5744
  have eq5757 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5755 X0
       have j1 := eq12 (σ y) (σ X0)
       grind)
    | (have r₁ := eq5755 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq5755 X0
       have r₂ := eq12 (σ y) (σ X0)
       grind)
    | exact resolve eq5755 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5755
  have eq5776 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq5757
    | (have j0 := eq5757 X0
       grind)
    | exact resolve eq5757 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq5757
  have eq11181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) ∨ (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) = (k (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq1170 (M.op (M.op X0 X0) X1) X0 (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))
       grind)
    | exact superpose eq1170 eq736
    | (have j0 := eq736 X0 X1
       grind)
    | exact resolve eq736 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq11182 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11181 X0 X1
       have i₂ := eq1170 (M.op (M.op X0 X0) X1) X0 (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))
       grind)
    | exact superpose eq1170 eq11181
    | (have j0 := eq11181 X0 X1
       grind)
    | exact resolve eq11181 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11181
  have eq11253 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)))) ∨ (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) = (M.op (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)))) ∨ (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq565 (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))
       have i₂ := eq11182 X0 X1
       grind)
    | exact superpose eq11182 eq565
    | (have j0 := eq565 (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))
       have j1 := eq11182 X0 X1
       grind)
    | exact resolve eq565 eq11182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq11182
  have eq11256 : ∀ X0 X1 : G, (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) = (M.op (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)))) ∨ (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11253 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11253
  have eq12007 : (τ (σ (M.op x y))) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq90 eq53
    | exact resolve eq53 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12018 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq12019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq12018
    | exact resolve eq12018 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12018
  have eq12026 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq12007
    | exact resolve eq12007 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12007
  have eq12030 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq12019
       have r₂ := eq27
       grind)
    | exact resolve eq12019 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12019
  have eq12032 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq12030
    | exact resolve eq12030 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12030
  have eq12034 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq12032 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq12032
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq12032
       grind)
    | exact resolve eq13 eq12032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12032
  have eq12082 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq12034 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034
  have eq12115 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq12082 eq102
    | exact resolve eq102 eq12082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12151 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq12082 eq328
    | exact resolve eq328 eq12082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12082
  have eq12163 : ∀ X0 : G, y = (k X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq12151
    | exact resolve eq12151 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12151
  have eq12173 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq12115
    | exact resolve eq12115 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12115
  have eq12199 : ∀ X0 : G, y = (k X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12163 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq12163 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq12163 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12163
  have eq12202 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3241 y
       grind)
    | (have r₁ := eq12173
       have r₂ := eq3241 y
       grind)
    | exact resolve eq12173 eq3241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3241 eq12173
  have eq12360 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq567 y
       have i₂ := eq12199 y
       grind)
    | exact superpose eq12199 eq567
    | (have j0 := eq567 y
       grind)
    | exact resolve eq567 eq12199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq12375 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34 X0 y
       have i₂ := eq12199 (τ X0)
       grind)
    | exact superpose eq12199 eq34
    | exact resolve eq34 eq12199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12391 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12360
  have eq12398 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12375 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12375
    | (have j0 := eq12375 X0
       grind)
    | exact resolve eq12375 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12375
  have eq12410 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12391
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12391
    | exact resolve eq12391 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12391
  have eq12491 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1074 X0 y x
       have i₂ := eq12202
       grind)
    | exact superpose eq12202 eq1074
    | exact resolve eq1074 eq12202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12624 : ∀ X0 : G, (σ y) = (σ (k X0 y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40 eq12398
    | exact resolve eq12398 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq12660 : (τ (k (σ y) (σ y))) = (k (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12398 eq623
    | exact resolve eq623 eq12398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12709 : (k y y) = (k (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102 eq12660
    | exact resolve eq12660 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12660
  have eq12886 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12410 eq1074
    | exact resolve eq1074 eq12410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14437 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12491 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12491
    | (have j0 := eq12491 x X0
       grind)
    | exact resolve eq12491 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12491
  have eq14706 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12202
       have i₂ := eq14437 y
       grind)
    | exact superpose eq14437 eq12202
    | exact resolve eq12202 eq14437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12202 eq14437
  have eq14712 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq14706
  have eq14730 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ x) X0) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14712 eq1199
    | exact resolve eq1199 eq14712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14732 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq378 eq14730
    | (have j0 := eq14730 (σ y)
       grind)
    | exact resolve eq14730 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14730
  have eq15832 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq12886
    | (have j0 := eq12886 (σ x) X0
       grind)
    | exact resolve eq12886 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12886
  have eq16115 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15832 eq12410
    | exact resolve eq12410 eq15832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12410 eq15832
  have eq16120 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16115
  have eq16128 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16120 eq27
    | exact resolve eq27 eq16120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16120
  have eq17404 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (k (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq487 X0
       have i₂ := eq12199 y
       grind)
    | exact superpose eq12199 eq487
    | exact resolve eq487 eq12199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq12199
  have eq17431 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ y)))) = (τ (k X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17404 X0
       have i₂ := eq494 X0
       grind)
    | exact superpose eq494 eq17404
    | exact resolve eq17404 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17404
  have eq19915 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14712 eq14732
    | exact resolve eq14732 eq14712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14732
  have eq19935 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19915
  have eq24189 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19935
       have i₂ := eq1074 sF2 sF2 x
       grind)
    | (have i₁ := eq19935
       have i₂ := eq1074 X0 sF2 sF2
       grind)
    | exact superpose eq1074 eq19935
    | exact resolve eq19935 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19935
  have eq26213 : ∀ X0 : G, (τ (k (σ x) (σ y))) = (k x (k X0 (τ (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12398 eq1945
    | exact resolve eq1945 eq12398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945 eq12398
  have eq26267 : ∀ X0 : G, (τ (k (σ x) (σ y))) = (k x (k X0 y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq26213
    | exact resolve eq26213 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26213
  have eq26305 : ∀ X0 : G, (k x y) = (k x (k X0 y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq53 eq26267
    | exact resolve eq26267 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26267
  have eq28529 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f28529_14 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
      intro X0 X1 X2
      grind
    have f28529_15 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f28529_24 : (σ x) ≠ (M.op X0 (M.op X1 (σ x))) := by grind
    have f28529_25 : x ≠ (M.op x y) := by grind
    have f28529_26 : y ≠ (M.op x y) := by grind
    have f28529_27 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
      intro X0
      first
      | (have j0 := f28529_15 X0
         grind)
      | (have r₁ := f28529_15 X0
         have r₂ := f28529_25
         grind)
      | exact resolve f28529_15 f28529_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f28529_28 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
      intro X0
      first
      | (have j0 := f28529_27 X0
         grind)
      | (have r₁ := f28529_27 X0
         have r₂ := f28529_26
         grind)
      | exact resolve f28529_27 f28529_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f28529_32 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (σ x))) := by
      intro X0 X1
      first
      | (have i₁ := f28529_14 X0 (M.op (σ x) (σ x)) x
         have i₂ := f28529_28 (M.op (σ x) (σ x))
         grind)
      | exact superpose f28529_28 f28529_14
      | exact resolve f28529_14 f28529_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f28529_40 : (σ x) ≠ (σ x) := by
      first
      | (have i₁ := f28529_24
         have i₂ := f28529_32 X0 X1
         grind)
      | exact superpose f28529_32 f28529_24
      | (have r₁ := f28529_24
         have r₂ := f28529_32 X0 X1
         grind)
      | exact resolve f28529_24 f28529_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f28529_41 : False := by grind
    exact f28529_41
  have eq45731 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X2)) (σ x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3567 X2 (M.op X1 X1)
       have i₂ := eq1074 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq3567 X2 (M.op X1 X1)
       have i₂ := eq1074 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq1074 eq3567
    | exact resolve eq3567 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567
  have eq45969 : ∀ X0 X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op (M.op x y) x) X2)) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3568 X2 (M.op X1 X1)
       have i₂ := eq1074 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq3568 X2 (M.op X1 X1)
       have i₂ := eq1074 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq1074 eq3568
    | exact resolve eq3568 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568
  have eq65759 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ x)) X1)) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) X1)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq14712 eq845
    | exact resolve eq845 eq14712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq66070 : ∀ X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X1)) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq65759 x X1
       have i₂ := eq357 sF2 X1 x
       grind)
    | exact superpose eq357 eq65759
    | exact resolve eq65759 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq65759
  have eq207068 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq66070 sF2
       have i₂ := eq62 sF2 X1 sF2
       grind)
    | (have i₁ := eq66070 X0
       have i₂ := eq62 X0 sF2 x
       grind)
    | exact superpose eq62 eq66070
    | exact resolve eq66070 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66070
  have eq326456 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4⟩ := hcon
    have f326456_16 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
      intro X0 X1
      grind
    have f326456_17 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f326456_26 : X0 ≠ (M.op (σ x) (M.op (σ x) X0)) := by grind
    have f326456_29 : x ≠ (M.op x y) := by grind
    have f326456_30 : y ≠ (M.op x y) := by grind
    have f326456_31 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
      intro X0
      first
      | (have j0 := f326456_17 X0
         grind)
      | (have r₁ := f326456_17 X0
         have r₂ := f326456_29
         grind)
      | exact resolve f326456_17 f326456_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f326456_32 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ y = (M.op x y) := by
      intro X0 X1
      first
      | (have j0 := f326456_16 X0 X1
         grind)
      | (have r₁ := f326456_16 X0 X1
         have r₂ := f326456_29
         grind)
      | exact resolve f326456_16 f326456_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f326456_33 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
      intro X0
      first
      | (have j0 := f326456_31 X0
         grind)
      | (have r₁ := f326456_31 X0
         have r₂ := f326456_30
         grind)
      | exact resolve f326456_31 f326456_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f326456_34 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
      intro X0 X1
      first
      | (have j0 := f326456_32 X0 X1
         grind)
      | (have r₁ := f326456_32 X0 X1
         have r₂ := f326456_30
         grind)
      | exact resolve f326456_32 f326456_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f326456_38 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
      intro X0
      first
      | (have i₁ := f326456_34 X0 (M.op (σ x) (σ x))
         have i₂ := f326456_33 X0
         grind)
      | exact superpose f326456_33 f326456_34
      | exact resolve f326456_34 f326456_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f326456_41 : X0 ≠ X0 := by
      first
      | (have i₁ := f326456_26
         have i₂ := f326456_38 X0
         grind)
      | exact superpose f326456_38 f326456_26
      | (have r₁ := f326456_26
         have r₂ := f326456_38 X0
         grind)
      | exact resolve f326456_26 f326456_38
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f326456_43 : False := by grind
    exact f326456_43
  clear eq24189 eq207068
  have eq327978 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq326456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326456
  have eq328047 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq327978
    | (have j0 := eq327978 (σ y)
       grind)
    | exact resolve eq327978 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327978
  have eq328568 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14712 eq328047
    | exact resolve eq328047 eq14712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14712 eq328047
  have eq328686 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq328568
  have eq328715 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq328686 eq28529
    | exact resolve eq28529 eq328686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28529 eq328686
  have eq328941 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq328715 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328715
  have eq330361 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq328941 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq328941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2469334 : ∀ X0 : G, (τ (k (σ y) (σ y))) ≠ (τ (k (k (σ y) (σ y)) (σ y))) ∨ (τ (k (σ y) (σ y))) = (k X0 (τ (k (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17431 eq2409
    | (have j0 := eq2409 (k (σ y) (σ y)) X0
       grind)
    | exact resolve eq2409 eq17431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409 eq17431
  have eq2470348 : ∀ X0 : G, (τ (k (σ y) (σ y))) ≠ (k (k y y) y) ∨ (τ (k (σ y) (σ y))) = (k X0 (τ (k (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq623 eq2469334
    | (have j0 := eq2469334 X0
       grind)
    | exact resolve eq2469334 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq2469334
  have eq2470371 : ∀ X0 : G, (k y y) ≠ (k (k y y) y) ∨ (τ (k (σ y) (σ y))) = (k X0 (τ (k (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq102 eq2470348
    | (have j0 := eq2470348 X0
       grind)
    | exact resolve eq2470348 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470348
  have eq2470382 : ∀ X0 : G, (τ (k (σ y) (σ y))) = (k X0 (τ (k (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2470371 X0
       grind)
    | (have r₁ := eq2470371 X0
       have r₂ := eq12709
       grind)
    | exact resolve eq2470371 eq12709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12709 eq2470371
  have eq2470392 : ∀ X0 : G, (k y y) = (k X0 (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq102 eq2470382
    | exact resolve eq2470382 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq2470382
  have eq2475002 : (k x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26305 y
       have i₂ := eq2470392 x
       grind)
    | exact superpose eq2470392 eq26305
    | exact resolve eq26305 eq2470392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26305 eq2470392
  have eq2475705 : (k x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2475002
  have eq2480123 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5776 y
       have i₂ := eq2475705
       grind)
    | exact superpose eq2475705 eq5776
    | (have j0 := eq5776 y
       grind)
    | exact resolve eq5776 eq2475705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5776 eq2475705
  have eq2480542 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2480123
       have r₂ := eq12624 x
       grind)
    | exact resolve eq2480123 eq12624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12624 eq2480123
  have eq2480756 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2480542
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2480542
    | exact resolve eq2480542 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480542
  have eq2480810 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2480756
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq2480756
    | exact resolve eq2480756 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480756
  have eq2480831 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2480810
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2480810
    | exact resolve eq2480810 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480810
  have eq2480837 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2480831
       have r₂ := eq111
       grind)
    | exact resolve eq2480831 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq2480831
  have eq2549700 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2480837 eq53
    | exact resolve eq53 eq2480837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2480837
  have eq2709996 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq328941 eq2549700
    | exact resolve eq2549700 eq328941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328941
  have eq2710632 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2709996
  have eq2710648 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq2710632
    | exact resolve eq2710632 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710632
  have eq2710740 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12026
       have i₂ := eq2710648
       grind)
    | exact superpose eq2710648 eq12026
    | exact resolve eq12026 eq2710648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710648
  have eq2710943 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2710740
  have eq2711240 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2710943
       grind)
    | exact superpose eq2710943 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq2710943
       grind)
    | exact resolve eq13 eq2710943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710943
  have eq2711791 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2711240 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711240
  have eq2713126 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34 X0 y
       have i₂ := eq2711791 (τ X0)
       grind)
    | exact superpose eq2711791 eq34
    | exact resolve eq34 eq2711791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq2711791
  have eq2713809 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2713126 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2713126
    | (have j0 := eq2713126 X0
       grind)
    | exact resolve eq2713126 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2713126
  have eq2714650 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2713809 X0
       have j1 := eq330361 X0
       grind)
    | (have r₁ := eq2713809 X0
       have r₂ := eq330361 X0
       grind)
    | exact resolve eq2713809 eq330361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330361 eq2713809
  have eq2715362 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2714650 eq3596
    | (have j0 := eq3596 (σ y)
       grind)
    | exact resolve eq3596 eq2714650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714650
  have eq2716006 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2715362
  have eq2716213 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2716006
    | exact resolve eq2716006 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716006
  have eq2726089 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1074 X0 y x
       have i₂ := eq2716213
       grind)
    | exact superpose eq2716213 eq1074
    | exact resolve eq1074 eq2716213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2812383 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2726089 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2726089
    | (have j0 := eq2726089 x X0
       grind)
    | exact resolve eq2726089 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2726089
  have eq2819667 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2716213
       have i₂ := eq2812383 y
       grind)
    | exact superpose eq2812383 eq2716213
    | exact resolve eq2716213 eq2812383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716213 eq2812383
  have eq2820080 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2819667
  have eq2820949 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2820080 eq20
    | exact resolve eq20 eq2820080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2821014 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2820080 eq495
    | exact resolve eq495 eq2820080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq2821993 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2820080
  have eq2822489 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2821014 X0
       have i₂ := eq494 X0
       grind)
    | exact superpose eq494 eq2821014
    | exact resolve eq2821014 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq2821014
  have eq2822546 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2820949
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2820949
    | exact resolve eq2820949 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820949
  have eq2822551 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2822546 eq26
    | exact resolve eq26 eq2822546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2822875 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2822546 eq16128
    | (have r₁ := eq16128
       have r₂ := eq2822546
       grind)
    | exact resolve eq16128 eq2822546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16128
  have eq2823680 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2822875
  have eq2823681 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2823680
  have eq2823986 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2823681 eq27
    | exact resolve eq27 eq2823681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2823996 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X1) (M.op (M.op (σ x) (σ x)) X0)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2823681 eq861
    | exact resolve eq861 eq2823681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq2824002 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ x) X0) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2823681 eq1199
    | exact resolve eq1199 eq2823681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq2824025 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op (σ x) (σ x)) X2)) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq2823681 eq45731
    | exact resolve eq45731 eq2823681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45731
  have eq2824149 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op X2 (σ x)) ∨ x = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq2824025 x x x
       have i₂ := eq1124 x x sF2 x
       grind)
    | exact superpose eq1124 eq2824025
    | exact resolve eq2824025 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824025
  have eq2824152 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq378 eq2824002
    | (have j0 := eq2824002 (σ y)
       grind)
    | exact resolve eq2824002 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq2824002
  have eq2824158 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2823996 x x
       have i₂ := eq987 sF2 x x
       grind)
    | exact superpose eq987 eq2823996
    | exact resolve eq2823996 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987 eq2823996
  have eq2841174 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2824149 eq2824152
    | exact resolve eq2824152 eq2824149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824149 eq2824152
  have eq2841369 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq2841174
  have eq2848779 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2841369
       have i₂ := eq1074 sF2 sF2 x
       grind)
    | (have i₁ := eq2841369
       have i₂ := eq1074 X0 sF2 sF2
       grind)
    | exact superpose eq1074 eq2841369
    | exact resolve eq2841369 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2841369
  have eq2850460 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2848779 eq1170
    | exact resolve eq1170 eq2848779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq2863772 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (k (σ X0) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2822489 eq328
    | exact resolve eq328 eq2822489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822489
  have eq2864915 : ∀ X0 : G, (k X0 (τ (σ (M.op x y)))) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2863772 X0
       have i₂ := eq328 X0 sF1
       grind)
    | exact superpose eq328 eq2863772
    | exact resolve eq2863772 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863772
  have eq2864947 : ∀ X0 : G, (k X0 y) = (k X0 (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq2864915
    | exact resolve eq2864915 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864915
  have eq2864963 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq2864947
    | exact resolve eq2864947 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2864947
  have eq2879326 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2824158 sF2
       have i₂ := eq62 sF2 X1 sF2
       grind)
    | (have i₁ := eq2824158 X0
       have i₂ := eq62 X0 sF2 x
       grind)
    | exact superpose eq62 eq2824158
    | exact resolve eq2824158 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2824158
  have eq2906659 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2848779 eq2879326
    | exact resolve eq2879326 eq2848779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848779 eq2879326
  have eq2910907 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2906659 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2906659
  have eq2911089 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2822551 eq2910907
    | exact resolve eq2910907 eq2822551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822551
  have eq2911095 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2910907
    | (have j0 := eq2910907 (σ y)
       grind)
    | exact resolve eq2910907 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2910907
  have eq2911572 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq2911089
  have eq2911658 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2823681 eq2911095
    | exact resolve eq2911095 eq2823681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911095
  have eq2911996 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2911658
  have eq2912046 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2823681 eq2911572
    | exact resolve eq2911572 eq2823681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823681 eq2911572
  have eq2912404 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2912046
  have eq2912520 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2911996 eq2850460
    | exact resolve eq2850460 eq2911996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911996
  have eq2913116 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2912520 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2912520
  have eq2913289 : ∀ X0 : G, (σ x) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2912404 eq2850460
    | exact resolve eq2850460 eq2912404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2850460 eq2912404
  have eq2913889 : ∀ X0 : G, (σ x) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2913289 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2913289
  have eq2915893 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2913116 eq2549700
    | exact resolve eq2549700 eq2913116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549700 eq2913116
  have eq2916076 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2915893
  have eq2917054 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq2916076
    | exact resolve eq2916076 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916076
  have eq2922233 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2913889 eq175
    | exact resolve eq175 eq2913889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2913889
  have eq2923421 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2922233
       have r₂ := eq2823986
       grind)
    | exact resolve eq2922233 eq2823986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922233
  have eq2923518 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq2923421
    | exact resolve eq2923421 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923421
  have eq2927936 : x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2923518 eq2864963
    | exact resolve eq2864963 eq2923518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923518
  have eq2928177 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq2927936
  have eq3009657 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2917054
       grind)
    | exact superpose eq2917054 eq44
    | exact resolve eq44 eq2917054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2917054
  have eq3010099 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3009657
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3009657
    | exact resolve eq3009657 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009657
  have eq3011320 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2822546 eq3010099
    | exact resolve eq3010099 eq2822546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822546 eq3010099
  have eq3011600 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3011320
  have eq3011647 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3011600
       have r₂ := eq2823986
       grind)
    | exact resolve eq3011600 eq2823986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823986 eq3011600
  have eq3011654 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3011647 eq57
    | exact resolve eq57 eq3011647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq3011647
  have eq3011869 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq3011654
    | exact resolve eq3011654 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3011654
  have eq3012011 : x = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3011869 eq2864963
    | exact resolve eq2864963 eq3011869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864963 eq3011869
  have eq3012073 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq3012011
  have eq3012420 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12026
       have i₂ := eq3012073
       grind)
    | exact superpose eq3012073 eq12026
    | exact resolve eq12026 eq3012073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12026 eq3012073
  have eq3012631 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq3012420
  have eq3013276 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq3012631
       grind)
    | exact superpose eq3012631 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq3012631
       grind)
    | exact resolve eq13 eq3012631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3012631
  have eq3013850 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3013276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3013276
  have eq3014543 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2928177
       have i₂ := eq3013850 sF0
       grind)
    | exact superpose eq3013850 eq2928177
    | exact resolve eq2928177 eq3013850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928177 eq3013850
  have eq3015257 : x = y ∨ x = (M.op x y) := by grind
  clear eq3014543
  have eq3015860 : x = (M.op x y) := by
    first
    | (have r₁ := eq3015257
       have r₂ := eq2821993
       grind)
    | exact resolve eq3015257 eq2821993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821993 eq3015257
  have eq3016890 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3015860 eq20
    | exact resolve eq20 eq3015860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3016972 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op X0 (M.op X1 X1)) x)) := by
    intro X0 X1
    first
    | exact superpose eq3015860 eq1126
    | exact resolve eq1126 eq3015860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq3017548 : ∀ X0 X1 X2 : G, (M.op x x) = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op x x) X2)) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq3015860 eq45969
    | exact resolve eq45969 eq3015860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45969
  have eq3017567 : ∀ X2 : G, (M.op x x) = (M.op X2 x) := by
    intro X2
    first
    | (have i₁ := eq3017548 x x X2
       have i₂ := eq1124 x x x X2
       grind)
    | exact superpose eq1124 eq3017548
    | exact resolve eq3017548 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124 eq3017548
  have eq3018055 : x = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq3016972 x x
       have i₂ := eq1119 x x
       grind)
    | exact superpose eq1119 eq3016972
    | exact resolve eq3016972 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq3016972
  have eq3018126 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3016890
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3016890
    | exact resolve eq3016890 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016890
  have eq3018130 : x = (M.op x (M.op x x)) := by
    first
    | exact superpose eq3015860 eq3018055
    | exact resolve eq3018055 eq3015860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018055
  have eq3018144 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3018126 eq26
    | exact resolve eq26 eq3018126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3022179 : ∀ X0 : G, x = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq3018130
       have i₂ := eq1074 x x X0
       grind)
    | (have i₁ := eq3018130
       have i₂ := eq1074 X0 x x
       grind)
    | exact superpose eq1074 eq3018130
    | exact resolve eq3018130 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq3022196 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1112 x x X0 X1
       have i₂ := eq3018130
       grind)
    | exact superpose eq3018130 eq1112
    | exact resolve eq1112 eq3018130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq3018130
  have eq3038451 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3022196 X0 (M.op x x)
       have i₂ := eq3022179 X0
       grind)
    | exact superpose eq3022179 eq3022196
    | exact resolve eq3022196 eq3022179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022196
  have eq3041964 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3038451 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3038451
    | (have j0 := eq3038451 y
       grind)
    | exact resolve eq3038451 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3038451
  have eq3042403 : y = (M.op x x) := by
    first
    | exact superpose eq3015860 eq3041964
    | exact resolve eq3041964 eq3015860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015860 eq3041964
  have eq3042523 : ∀ X0 : G, x = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq3022179 X0
       have i₂ := eq3042403
       grind)
    | exact superpose eq3042403 eq3022179
    | exact resolve eq3022179 eq3042403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022179
  have eq3046482 : ∀ X0 : G, x ≠ y ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq3042523 y
       grind)
    | exact superpose eq3042523 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq3042523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3046778 : ∀ X0 : G, (σ (M.op (M.op x X0) x)) = (M.op (σ (M.op (M.op x X0) x)) (σ (M.op (M.op x X0) x))) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x X0) x))) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq11256 y x
       have i₂ := eq3042523 y
       grind)
    | exact superpose eq3042523 eq11256
    | exact resolve eq11256 eq3042523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11256
  have eq3048267 : ∀ X0 : G, (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x X0) x))) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3046778 y
       have i₂ := eq370 X0
       grind)
    | (have i₁ := eq3046778 X0
       have i₂ := eq370 X0
       grind)
    | exact superpose eq370 eq3046778
    | (have j0 := eq3046778 X0
       grind)
    | exact resolve eq3046778 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046778
  have eq3048508 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x X0) x))) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3048267 X0
       have i₂ := eq3017567 sF0
       grind)
    | exact superpose eq3017567 eq3048267
    | (have j0 := eq3048267 X0
       grind)
    | exact resolve eq3048267 eq3017567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048267
  have eq3048658 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x X0) x))) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3048508 X0
       have i₂ := eq3042403
       grind)
    | exact superpose eq3042403 eq3048508
    | (have j0 := eq3048508 X0
       grind)
    | exact resolve eq3048508 eq3042403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048508
  have eq3048744 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x X0) x))) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3048658 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3048658
    | (have j0 := eq3048658 X0
       grind)
    | exact resolve eq3048658 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048658
  have eq3048793 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op (M.op x y) x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3048744 X0
       have i₂ := eq370 X0
       grind)
    | (have i₁ := eq3048744 y
       have i₂ := eq370 X0
       grind)
    | exact superpose eq370 eq3048744
    | (have j0 := eq3048744 y
       grind)
    | exact resolve eq3048744 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048744
  have eq3048816 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3048793 X0
       have i₂ := eq3017567 sF0
       grind)
    | exact superpose eq3017567 eq3048793
    | (have j0 := eq3048793 X0
       grind)
    | exact resolve eq3048793 eq3017567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048793
  have eq3048826 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3048816 X0
       have i₂ := eq3042403
       grind)
    | exact superpose eq3042403 eq3048816
    | (have j0 := eq3048816 X0
       grind)
    | exact resolve eq3048816 eq3042403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048816
  have eq3048832 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3048826 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3048826
    | (have j0 := eq3048826 X0
       grind)
    | exact resolve eq3048826 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048826
  have eq3048835 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3048832 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3048832
    | (have j0 := eq3048832 X0
       grind)
    | exact resolve eq3048832 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048832
  have eq3048838 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | exact superpose eq26 eq3048835
    | (have j0 := eq3048835 X0
       grind)
    | exact resolve eq3048835 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3048835
  have eq3048841 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | exact superpose eq3018126 eq3048838
    | (have j0 := eq3048838 X0
       grind)
    | exact resolve eq3048838 eq3018126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048838
  have eq3048843 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq3048841 X0
       grind)
    | (have r₁ := eq3048841 X0
       have r₂ := eq27
       grind)
    | exact resolve eq3048841 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048841
  have eq3048845 : x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3048843 x
       have i₂ := eq370 x
       grind)
    | (have i₁ := eq3048843 y
       have i₂ := eq370 x
       grind)
    | exact superpose eq370 eq3048843
    | (have j0 := eq3048843 y
       grind)
    | exact resolve eq3048843 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq3048843
  have eq3048846 : x = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3048845
       have i₂ := eq3017567 sF0
       grind)
    | exact superpose eq3017567 eq3048845
    | exact resolve eq3048845 eq3017567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017567 eq3048845
  have eq3048847 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3048846
       have i₂ := eq3042403
       grind)
    | exact superpose eq3042403 eq3048846
    | exact resolve eq3048846 eq3042403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042403 eq3048846
  have eq3058300 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3048847 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq3048847
       grind)
    | exact resolve eq13 eq3048847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048847
  have eq3058791 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq3058300 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3058300
  have eq3063638 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = y := by
    first
    | exact superpose eq3058791 eq3596
    | (have j0 := eq3596 (σ y)
       grind)
    | exact resolve eq3596 eq3058791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596
  have eq3063899 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3058791 eq328
    | exact resolve eq328 eq3058791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq3058791
  have eq3064289 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = y := by grind
  clear eq3063638
  have eq3064493 : ∀ X0 : G, y = (k X0 y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29 eq3063899
    | exact resolve eq3063899 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063899
  have eq3064558 : y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq29 eq3064289
    | exact resolve eq3064289 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3064289
  have eq3064788 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq3064493 X0
       have j1 := eq3046482 X0
       grind)
    | (have r₁ := eq3064493 X0
       have r₂ := eq3046482 X0
       grind)
    | exact resolve eq3064493 eq3046482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046482 eq3064493
  have eq3064834 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3064558
       have i₂ := eq3042523 y
       grind)
    | exact superpose eq3042523 eq3064558
    | exact resolve eq3064558 eq3042523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042523 eq3064558
  have eq3064835 : x = y := by grind
  clear eq3064834
  have eq3065176 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3064835
       grind)
    | exact superpose eq3064835 eq24
    | exact resolve eq24 eq3064835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3066913 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3065176
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3065176
    | exact resolve eq3065176 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065176
  have eq3067483 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3018126 eq3066913
    | exact resolve eq3066913 eq3018126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3066913
  have eq3068681 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3067483 eq3018144
    | exact resolve eq3018144 eq3067483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018144 eq3067483
  have eq3069204 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq3064788 X0
       have i₂ := eq3064835
       grind)
    | exact superpose eq3064835 eq3064788
    | exact resolve eq3064788 eq3064835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3064788 eq3064835
  have eq3075171 : (k (M.op x y) x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3018126 eq169
    | exact resolve eq169 eq3018126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq3075172 : x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3075171
       have i₂ := eq3069204 sF0
       grind)
    | exact superpose eq3069204 eq3075171
    | exact resolve eq3075171 eq3069204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3069204 eq3075171
  have eq3075173 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3018126 eq3075172
    | exact resolve eq3075172 eq3018126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075172
  have eq3075174 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3018126 eq3075173
    | exact resolve eq3075173 eq3018126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075173
  have eq3075175 : x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3075174
  have eq3075188 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3075175 eq15
    | exact resolve eq15 eq3075175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075175
  have eq3076366 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3075188
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3075188
    | exact resolve eq3075188 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3075188
  have eq3076846 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3018126 eq3076366
    | exact resolve eq3076366 eq3018126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018126 eq3076366
  have eq3076847 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3076846
  have eq3081959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3076847 eq3068681
    | exact resolve eq3068681 eq3076847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068681 eq3076847
  have eq3081960 : False := by grind
  exact eq3081960
