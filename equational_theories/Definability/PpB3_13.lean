import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  clear eq30
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq119 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq103 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq103 X0 X1 X2 X3
       grind)
    | exact superpose eq103 eq103
    | exact resolve eq103 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq103 X0 X1 X2 X3
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq124 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq124
    | exact resolve eq124 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq119 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq300 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq106
    | (have j0 := eq106 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq106 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq405 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq103 X0 X0 x X0
       have i₂ := eq128 X0 X0 x
       grind)
    | exact superpose eq128 eq103
    | exact resolve eq103 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq128 X0 X0 X0
       have i₂ := eq405 X0
       grind)
    | exact superpose eq405 eq128
    | exact resolve eq128 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq421 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X0 X0 X1
       have i₂ := eq405 X0
       grind)
    | exact superpose eq405 eq103
    | exact resolve eq103 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq405
  have eq475 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq9
    | exact resolve eq9 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq475 X0 X1
       have i₂ := eq127 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq475 X0 X1
       have i₂ := eq127 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq127 eq475
    | exact resolve eq475 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq694 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq487 X0 X1
       grind)
    | exact superpose eq487 eq9
    | exact resolve eq9 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq694
    | exact resolve eq694 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq694
  have eq710 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 X1
       have i₂ := eq705 X0 X1
       grind)
    | exact superpose eq705 eq487
    | exact resolve eq487 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq711 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 X1
       have i₂ := eq705 X0 (M.op X0 X1)
       grind)
    | exact superpose eq705 eq421
    | exact resolve eq421 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq713 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq705 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq705
    | exact resolve eq705 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq705 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq705
    | exact resolve eq705 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq760 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op X0 (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq711 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq711
    | exact resolve eq711 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16002 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq300 x y
       grind)
    | exact superpose eq300 eq16
    | (have j1 := eq300 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq300 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq300 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq300 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq16053 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq16002
  have eq20729 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op (M.op X0 X1) X0) X2)
       have i₂ := eq760 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq760 eq9
    | exact resolve eq9 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20783 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3))) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3))
       have i₂ := eq760 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq760 eq9
    | exact resolve eq9 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20814 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20729 X0 X1 X2
       have i₂ := eq711 X0 X1
       grind)
    | exact superpose eq711 eq20729
    | exact resolve eq20729 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20729
  have eq20955 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20814 (M.op X0 X1) X2 X0
       have i₂ := eq711 X0 X1
       grind)
    | exact superpose eq711 eq20814
    | exact resolve eq20814 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq21009 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X0) X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) (M.op X1 X0) X0
       have i₂ := eq20814 X1 X0 X2
       grind)
    | exact superpose eq20814 eq9
    | exact resolve eq9 eq20814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21232 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X0) = (M.op X1 (M.op (M.op (M.op X1 X2) X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq760 X0 (M.op (M.op X0 X1) X2) X2
       have i₂ := eq20955 X0 X1 X2
       grind)
    | exact superpose eq20955 eq760
    | exact resolve eq760 eq20955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq20955
  have eq21842 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20783 (M.op X1 X0) X1 X2 X0
       have i₂ := eq20814 X1 X0 X2
       grind)
    | exact superpose eq20814 eq20783
    | exact resolve eq20783 eq20814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20814
  have eq21892 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X1) X2)) X3)) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20783 X0 (M.op (M.op X0 X1) X1) X2 X3
       have i₂ := eq21009 X1 X0 (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X1) X2)) X3)
       grind)
    | exact superpose eq21009 eq20783
    | exact resolve eq20783 eq21009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21009
  have eq22270 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 (M.op (M.op X0 X1) X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq713 (M.op X0 (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq21842 X1 X0 (M.op X0 (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq21842 eq713
    | exact resolve eq713 eq21842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq22271 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 (M.op (M.op X0 X1) X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq714 (M.op X0 (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq21842 X1 X0 (M.op X0 (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq21842 eq714
    | exact resolve eq714 eq21842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq21842
  have eq205818 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op (M.op (M.op X0 X1) X1) X1) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21892 X0 X1 X1 X2
       have i₂ := eq21232 X1 X0 X1
       grind)
    | exact superpose eq21232 eq21892
    | exact resolve eq21892 eq21232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21232 eq21892
  have eq208190 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) X0) X0) (M.op X1 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20783 X1 (M.op (M.op (M.op X1 X0) X0) X0) X2 X0
       have i₂ := eq205818 X1 X0 X2
       grind)
    | exact superpose eq205818 eq20783
    | exact resolve eq20783 eq205818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20783 eq205818
  have eq209625 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op (M.op (M.op X0 X1) X1) X1) (M.op X0 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22270 (M.op (M.op (M.op X0 X1) X1) X1) (M.op X0 X1) X2
       have i₂ := eq208190 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq208190 eq22270
    | exact resolve eq22270 eq208190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22270 eq208190
  have eq499795 : ∀ X0 : G, (M.op (τ (M.op (σ y) (M.op (σ y) (σ x)))) X0) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22271 (σ y) (σ x) X0
       have i₂ := eq16053
       grind)
    | exact superpose eq16053 eq22271
    | exact resolve eq22271 eq16053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22271
  have eq500217 : ∀ X0 : G, (M.op (τ (M.op (σ y) (σ x))) X0) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq499795 X0
       have i₂ := eq127 (σ y) (σ x)
       grind)
    | (have i₁ := eq499795 X0
       have i₂ := eq127 (σ y) (M.op (σ y) (σ x))
       grind)
    | exact superpose eq127 eq499795
    | exact resolve eq499795 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499795
  have eq500363 : ∀ X0 : G, (M.op (τ (σ y)) X0) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16053 eq500217
    | exact resolve eq500217 eq16053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500217
  have eq500405 : ∀ X0 : G, y = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq500363 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq500363
    | exact resolve eq500363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500363
  have eq1092945 : ∀ X0 : G, y = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq127 y x
       have i₂ := eq500405 X0
       grind)
    | exact superpose eq500405 eq127
    | (have j1 := eq500405 y
       grind)
    | exact resolve eq127 eq500405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq500405
  have eq1236378 : y ≠ y ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have j0 := eq1092945 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092945
  have eq1236379 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1236378
  have eq1236916 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq705 y X0
       have i₂ := eq1236379
       grind)
    | exact superpose eq1236379 eq705
    | exact resolve eq705 eq1236379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236379
  have eq1238215 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1236916 eq16053
    | exact resolve eq16053 eq1236916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16053
  have eq1238217 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq1236916 X0
       grind)
    | exact superpose eq1236916 eq10
    | (have j1 := eq1236916 X0
       grind)
    | exact resolve eq10 eq1236916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236916
  have eq1238352 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1238215
  have eq1238435 : ∀ X0 : G, x = y ∨ (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1238217 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1238217
    | (have j0 := eq1238217 X0
       grind)
    | exact resolve eq1238217 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238217
  have eq1238436 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1238435 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238435
  have eq1238440 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq710 y x
       have i₂ := eq1238436 y
       grind)
    | exact superpose eq1238436 eq710
    | exact resolve eq710 eq1238436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq1238436
  have eq1241929 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op y y) (M.op X0 y))) X1) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq209625 X0 y X1
       have i₂ := eq1238440 (M.op X0 y)
       grind)
    | exact superpose eq1238440 eq209625
    | exact resolve eq209625 eq1238440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209625
  have eq1242523 : ∀ X0 X1 : G, (M.op (σ (M.op X0 y)) X1) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1241929 X0 X1
       have i₂ := eq705 y (M.op X0 y)
       grind)
    | exact superpose eq705 eq1241929
    | exact resolve eq1241929 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq1241929
  have eq1243152 : ∀ X1 : G, (M.op (σ y) X1) = X1 ∨ x = y := by
    intro X1
    first
    | exact superpose eq1238440 eq1242523
    | exact resolve eq1242523 eq1238440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238440 eq1242523
  have eq1244655 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1243152 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243152
  have eq1244805 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1244655 eq1238352
    | exact resolve eq1238352 eq1244655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238352 eq1244655
  have eq1246068 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1244805
  have eq1247604 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1246068
       grind)
    | exact superpose eq1246068 eq10
    | exact resolve eq10 eq1246068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246068
  have eq1247854 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1247604
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1247604
    | exact resolve eq1247604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247604
  have eq1247855 : x = y := by grind
  clear eq1247854
  have eq1247909 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1247855
       grind)
    | exact superpose eq1247855 eq16
    | exact resolve eq16 eq1247855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247855
  have eq1247910 : False := by grind
  exact eq1247910

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pyx_Equation2536 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  clear eq30
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq119 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq103 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq103 X0 X1 X2 X3
       grind)
    | exact superpose eq103 eq103
    | exact resolve eq103 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq103 X0 X1 X2 X3
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq124 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq124
    | exact resolve eq124 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq119 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq339 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq103 X0 X0 x X0
       have i₂ := eq128 X0 X0 x
       grind)
    | exact superpose eq128 eq103
    | exact resolve eq103 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq128 X0 X0 X0
       have i₂ := eq339 X0
       grind)
    | exact superpose eq339 eq128
    | exact resolve eq128 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq355 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X0 X0 X1
       have i₂ := eq339 X0
       grind)
    | exact superpose eq339 eq103
    | exact resolve eq103 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq339
  have eq408 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq9
    | exact resolve eq9 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 X1
       have i₂ := eq127 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq408 X0 X1
       have i₂ := eq127 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq127 eq408
    | exact resolve eq408 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq539 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq420 X0 X1
       grind)
    | exact superpose eq420 eq9
    | exact resolve eq9 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq547 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq539
    | exact resolve eq539 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq539
  have eq552 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 X1
       have i₂ := eq547 X0 (M.op X0 X1)
       grind)
    | exact superpose eq547 eq355
    | exact resolve eq355 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq554 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq547 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq547
    | exact resolve eq547 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq547 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq547
    | exact resolve eq547 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq591 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op X0 (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq552 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq552
    | exact resolve eq552 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq106
    | (have j0 := eq106 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq106 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq15498 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1196 x y
       grind)
    | exact superpose eq1196 eq16
    | (have j1 := eq1196 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1196 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1196 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1196 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq15549 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq15498
  have eq20527 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op (M.op X0 X1) X0) X2)
       have i₂ := eq591 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq591 eq9
    | exact resolve eq9 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20581 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3))) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3))
       have i₂ := eq591 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq591 eq9
    | exact resolve eq9 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq20612 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20527 X0 X1 X2
       have i₂ := eq552 X0 X1
       grind)
    | exact superpose eq552 eq20527
    | exact resolve eq20527 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq20527
  have eq21640 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20581 (M.op X1 X0) X1 X2 X0
       have i₂ := eq20612 X1 X0 X2
       grind)
    | exact superpose eq20612 eq20581
    | exact resolve eq20581 eq20612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20581 eq20612
  have eq22069 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 (M.op (M.op X0 X1) X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq555 (M.op X0 (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq21640 X1 X0 (M.op X0 (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq21640 eq555
    | exact resolve eq555 eq21640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq21640
  have eq499607 : ∀ X0 : G, (M.op (τ (M.op (σ y) (M.op (σ y) (σ x)))) X0) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22069 (σ y) (σ x) X0
       have i₂ := eq15549
       grind)
    | exact superpose eq15549 eq22069
    | exact resolve eq22069 eq15549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22069
  have eq500029 : ∀ X0 : G, (M.op (τ (M.op (σ y) (σ x))) X0) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq499607 X0
       have i₂ := eq127 (σ y) (σ x)
       grind)
    | (have i₁ := eq499607 X0
       have i₂ := eq127 (σ y) (M.op (σ y) (σ x))
       grind)
    | exact superpose eq127 eq499607
    | exact resolve eq499607 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499607
  have eq500175 : ∀ X0 : G, (M.op (τ (σ y)) X0) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq15549 eq500029
    | exact resolve eq500029 eq15549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500029
  have eq500217 : ∀ X0 : G, y = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq500175 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq500175
    | exact resolve eq500175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500175
  have eq1095281 : ∀ X0 : G, y = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq127 y x
       have i₂ := eq500217 X0
       grind)
    | exact superpose eq500217 eq127
    | (have j1 := eq500217 y
       grind)
    | exact resolve eq127 eq500217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq500217
  have eq1253214 : y ≠ y ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have j0 := eq1095281 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095281
  have eq1253215 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1253214
  have eq1253761 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq547 y X0
       have i₂ := eq1253215
       grind)
    | exact superpose eq1253215 eq547
    | exact resolve eq547 eq1253215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq1253215
  have eq1255076 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1253761 eq15549
    | exact resolve eq15549 eq1253761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15549
  have eq1255078 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq1253761 X0
       grind)
    | exact superpose eq1253761 eq10
    | (have j1 := eq1253761 X0
       grind)
    | exact resolve eq10 eq1253761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253761
  have eq1255217 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1255076
  have eq1255304 : ∀ X0 : G, x = y ∨ (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1255078 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1255078
    | (have j0 := eq1255078 X0
       grind)
    | exact resolve eq1255078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255078
  have eq1255305 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1255304 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255304
  have eq1255310 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq554 y X0
       have i₂ := eq1255305 y
       grind)
    | exact superpose eq1255305 eq554
    | exact resolve eq554 eq1255305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq1255305
  have eq1266149 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1255310 eq1255217
    | exact resolve eq1255217 eq1255310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255217 eq1255310
  have eq1266150 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1266149
  have eq1266153 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1266150
       grind)
    | exact superpose eq1266150 eq10
    | exact resolve eq10 eq1266150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266150
  have eq1266407 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1266153
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1266153
    | exact resolve eq1266153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266153
  have eq1266408 : x = y := by grind
  clear eq1266407
  have eq1266462 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1266408
       grind)
    | exact superpose eq1266408 eq16
    | exact resolve eq16 eq1266408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266408
  have eq1266463 : False := by grind
  exact eq1266463

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq1414 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1888 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1897 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1888 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1888
    | (have j0 := eq1888 X0 X1
       grind)
    | exact resolve eq1888 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1904 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1897 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq1897
    | (have j0 := eq1897 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq1897 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66417 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1414 X0 (σ X1)
       have i₂ := eq1904 X0 X1
       grind)
    | exact superpose eq1904 eq1414
    | (have j0 := eq1414 X0 (σ X1)
       have j1 := eq1904 X0 X1
       grind)
    | (have r₁ := eq1414 X0 (σ X1)
       have r₂ := eq1904 X0 X1
       grind)
    | (have r₁ := eq1414 X1 (σ X1)
       have r₂ := eq1904 X1 X1
       grind)
    | (have r₁ := eq1414 X0 X1
       have r₂ := eq1904 (σ (M.op X0 X0)) (M.op (σ X0) X1)
       grind)
    | exact resolve eq1414 eq1904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq66562 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1904 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq66564 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66417 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66417
  have eq66565 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66564 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66564
  have eq66704 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66565 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq66565
    | (have j0 := eq66565 X0 X1
       grind)
    | exact resolve eq66565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66565
  have eq66923 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq14 eq66704
    | (have j0 := eq66704 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq66704 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66704
  have eq67078 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66923 X0 X1
       have j1 := eq66562 X0 X1
       grind)
    | (have r₁ := eq66923 X0 X1
       have r₂ := eq66562 X0 X1
       grind)
    | (have r₁ := eq66923 X1 X1
       have r₂ := eq66562 X1 X1
       grind)
    | (have r₁ := eq66923 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq66562 X0 X1
       grind)
    | exact resolve eq66923 eq66562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66562 eq66923
  have eq978516 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq67078 x y
       grind)
    | exact superpose eq67078 eq16
    | (have j1 := eq67078 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq67078 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq67078 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq67078 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq67078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67078
  have eq979136 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq978516
  have eq979263 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq979136
       grind)
    | exact superpose eq979136 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq979136
       grind)
    | exact resolve eq13 eq979136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979723 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq979263
  have eq979724 : (M.op x x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq979723
  have eq980363 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1897 x y
       have i₂ := eq979724
       grind)
    | exact superpose eq979724 eq1897
    | (have j0 := eq1897 x y
       grind)
    | exact resolve eq1897 eq979724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897 eq979724
  have eq980366 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq980363
  have eq1081668 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq980366
       grind)
    | exact superpose eq980366 eq16
    | exact resolve eq16 eq980366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980366
  have eq1082627 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq979136 eq1081668
    | exact resolve eq1081668 eq979136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979136 eq1081668
  have eq1082628 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1082627
  have eq1083033 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1082628
       grind)
    | exact superpose eq1082628 eq10
    | exact resolve eq10 eq1082628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082628
  have eq1083226 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1083033
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1083033
    | exact resolve eq1083033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083033
  have eq1083227 : x = y := by grind
  clear eq1083226
  have eq1083230 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1083227
       grind)
    | exact superpose eq1083227 eq16
    | exact resolve eq16 eq1083227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083227
  have eq1083231 : False := by grind
  exact eq1083231

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation2536 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq125 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq103 X0 X1 X2 X3
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq129 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq125 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq125
    | exact resolve eq125 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq138 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 x) X0
       have r₂ := eq129 X0 x
       grind)
    | exact resolve eq13 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq142 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq1354 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq107
    | (have j0 := eq107 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq107 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27504 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1354 x y
       grind)
    | exact superpose eq1354 eq16
    | (have j1 := eq1354 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1354 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1354 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1354 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq27586 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq27504
  have eq507819 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq27586
       grind)
    | exact superpose eq27586 eq16
    | exact resolve eq16 eq27586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507841 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq142 (σ x) (σ y)
       have i₂ := eq27586
       grind)
    | exact superpose eq27586 eq142
    | exact resolve eq142 eq27586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27586
  have eq508174 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq507841
  have eq508338 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq508174
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq508174
    | exact resolve eq508174 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508174
  have eq508404 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14 eq508338
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq508338 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508338
  have eq508416 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq508404
       have r₂ := eq507819
       grind)
    | exact resolve eq508404 eq507819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507819 eq508404
  have eq508438 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq142 x y
       have i₂ := eq508416
       grind)
    | exact superpose eq508416 eq142
    | exact resolve eq142 eq508416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq508771 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq508438
  have eq509682 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 y x
       have i₂ := eq508771
       grind)
    | exact superpose eq508771 eq107
    | (have j0 := eq107 y x
       grind)
    | exact resolve eq107 eq508771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq508771
  have eq509685 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq509682
  have eq509694 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq509685
       grind)
    | exact superpose eq509685 eq16
    | exact resolve eq16 eq509685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509685
  have eq510216 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq508416 eq509694
    | exact resolve eq509694 eq508416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508416 eq509694
  have eq510217 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq510216
  have eq510292 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq510217
       grind)
    | exact superpose eq510217 eq10
    | exact resolve eq10 eq510217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510217
  have eq510447 : x = y ∨ x = y := by
    first
    | (have i₁ := eq510292
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq510292
    | exact resolve eq510292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510292
  have eq510448 : x = y := by grind
  clear eq510447
  have eq510451 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq510448
       grind)
    | exact superpose eq510448 eq16
    | exact resolve eq16 eq510448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510448
  have eq510452 : False := by grind
  exact eq510452

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxy_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  clear eq30
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq119 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq103 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq103 X0 X1 X2 X3
       grind)
    | exact superpose eq103 eq103
    | exact resolve eq103 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq103 X0 X1 X2 X3
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq124 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq124
    | exact resolve eq124 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq119 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq339 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq103 X0 X0 x X0
       have i₂ := eq128 X0 X0 x
       grind)
    | exact superpose eq128 eq103
    | exact resolve eq103 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq128 X0 X0 X0
       have i₂ := eq339 X0
       grind)
    | exact superpose eq339 eq128
    | exact resolve eq128 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq355 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X0 X0 X1
       have i₂ := eq339 X0
       grind)
    | exact superpose eq339 eq103
    | exact resolve eq103 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq339
  have eq408 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq9
    | exact resolve eq9 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 X1
       have i₂ := eq127 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq408 X0 X1
       have i₂ := eq127 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq127 eq408
    | exact resolve eq408 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq539 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq420 X0 X1
       grind)
    | exact superpose eq420 eq9
    | exact resolve eq9 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq547 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq539
    | exact resolve eq539 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq539
  have eq552 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 X1
       have i₂ := eq547 X0 (M.op X0 X1)
       grind)
    | exact superpose eq547 eq355
    | exact resolve eq355 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq554 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq547 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq547
    | exact resolve eq547 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq547 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq547
    | exact resolve eq547 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq591 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op X0 (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq552 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq552
    | exact resolve eq552 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1441 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq106
    | (have j0 := eq106 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq106 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq11666 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1441 x y
       grind)
    | exact superpose eq1441 eq16
    | (have j1 := eq1441 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1441 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1441 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1441 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq11712 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq11666
  have eq20555 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op (M.op X0 X1) X0) X2)
       have i₂ := eq591 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq591 eq9
    | exact resolve eq9 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20609 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3))) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3))
       have i₂ := eq591 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq591 eq9
    | exact resolve eq9 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq20639 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20555 X0 X1 X2
       have i₂ := eq552 X0 X1
       grind)
    | exact superpose eq552 eq20555
    | exact resolve eq20555 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq20555
  have eq21670 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20609 (M.op X1 X0) X1 X2 X0
       have i₂ := eq20639 X1 X0 X2
       grind)
    | exact superpose eq20639 eq20609
    | exact resolve eq20609 eq20639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20609 eq20639
  have eq22100 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 (M.op (M.op X0 X1) X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq555 (M.op X0 (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq21670 X1 X0 (M.op X0 (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq21670 eq555
    | exact resolve eq555 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq21670
  have eq340266 : ∀ X0 : G, (M.op (τ (M.op (σ x) (M.op (σ x) (σ y)))) X0) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22100 (σ x) (σ y) X0
       have i₂ := eq11712
       grind)
    | exact superpose eq11712 eq22100
    | exact resolve eq22100 eq11712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22100
  have eq340547 : ∀ X0 : G, (M.op (τ (M.op (σ x) (σ y))) X0) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq340266 X0
       have i₂ := eq127 (σ x) (σ y)
       grind)
    | (have i₁ := eq340266 X0
       have i₂ := eq127 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact superpose eq127 eq340266
    | exact resolve eq340266 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340266
  have eq340672 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11712 eq340547
    | exact resolve eq340547 eq11712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11712 eq340547
  have eq340710 : ∀ X0 : G, x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq340672 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq340672
    | exact resolve eq340672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340672
  have eq1127325 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq127 x y
       have i₂ := eq340710 X0
       grind)
    | exact superpose eq340710 eq127
    | (have j1 := eq340710 x
       grind)
    | exact resolve eq127 eq340710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq340710
  have eq1277020 : x ≠ x ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have j0 := eq1127325 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127325
  have eq1277021 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1277020
  have eq1277567 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq547 x X0
       have i₂ := eq1277021
       grind)
    | exact superpose eq1277021 eq547
    | exact resolve eq547 eq1277021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq1277021
  have eq1278888 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq1277567 X0
       grind)
    | exact superpose eq1277567 eq10
    | (have j1 := eq1277567 X0
       grind)
    | exact resolve eq10 eq1277567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277567
  have eq1279111 : ∀ X0 : G, x = y ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1278888 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1278888
    | (have j0 := eq1278888 X0
       grind)
    | exact resolve eq1278888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278888
  have eq1279112 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1279111 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279111
  have eq1279117 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq554 x X0
       have i₂ := eq1279112 x
       grind)
    | exact superpose eq1279112 eq554
    | exact resolve eq554 eq1279112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq1284366 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1279117 (σ y)
       grind)
    | exact superpose eq1279117 eq16
    | exact resolve eq16 eq1279117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279117
  have eq1286562 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq1279112 eq1284366
    | exact resolve eq1284366 eq1279112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279112 eq1284366
  have eq1286563 : x = y := by grind
  clear eq1286562
  have eq1287456 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1286563
       grind)
    | exact superpose eq1286563 eq16
    | exact resolve eq16 eq1286563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286563
  have eq1287457 : False := by grind
  exact eq1287457

/-- `Equation2588`: `x = (y ◇ ((z ◇ y) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyy_y_pxx_pxx_pyx_Equation2588 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2588 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2588.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq53 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq79
    | exact resolve eq79 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq80
    | exact resolve eq80 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq80
  have eq91 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq53
    | exact resolve eq53 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq91 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq53 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq53 eq91
    | exact resolve eq91 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq142 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq123 X0 X1
       have i₂ := eq83 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq83 eq123
    | exact resolve eq123 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq148 : ∀ X0 X1 : G, (M.op (σ (M.op X0 (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 X1
       have i₂ := eq53 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have i₁ := eq142 X0 X1
       have i₂ := eq53 X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq53 eq142
    | exact resolve eq142 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq142
  have eq546 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X2 X0) ∨ (M.op X1 X0) = (k X0 X2) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq12
    | (have j1 := eq14 X0 X1
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
  have eq11085 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq546 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq11086 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11085 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11085
  have eq11102 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11086 (σ X0) X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq11086
    | (have j0 := eq11086 (σ X0) X1
       grind)
    | exact resolve eq11086 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq11111 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq11086 X0 (τ X1)
       grind)
    | exact superpose eq11086 eq17
    | (have j1 := eq11086 X0 X1
       grind)
    | exact resolve eq17 eq11086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq11086
  have eq12356 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11111 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11111
    | (have j0 := eq11111 X1 X1
       grind)
    | exact resolve eq11111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11111
  have eq12714 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12356 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12356
    | (have j0 := eq12356 X0 X1
       grind)
    | exact resolve eq12356 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12356
  have eq13381 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq11102 X0 X1
       grind)
    | exact superpose eq11102 eq10
    | (have j1 := eq11102 X0 X1
       grind)
    | exact resolve eq10 eq11102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11102
  have eq13446 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13381 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13381
    | (have j0 := eq13381 X0 X1
       grind)
    | exact resolve eq13381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13381
  have eq13480 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13446 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13446
    | (have j0 := eq13446 X1 X1
       grind)
    | exact resolve eq13446 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13446
  have eq13942 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13480 y x
       grind)
    | exact superpose eq13480 eq16
    | (have j1 := eq13480 x x
       grind)
    | exact resolve eq16 eq13480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13480
  have eq14218 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13942
       have i₂ := eq12714 y x
       grind)
    | exact superpose eq12714 eq13942
    | (have j1 := eq12714 x x
       grind)
    | (have r₁ := eq13942
       have r₂ := eq12714 y x
       grind)
    | exact resolve eq13942 eq12714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12714 eq13942
  have eq14219 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq14218
  have eq14220 : x = (M.op x x) := by grind
  clear eq14219
  have eq14229 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 x x
       have i₂ := eq14220
       grind)
    | exact superpose eq14220 eq58
    | exact resolve eq58 eq14220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq14242 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq148 x X0
       have i₂ := eq14220
       grind)
    | exact superpose eq14220 eq148
    | exact resolve eq148 eq14220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq14419 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14242 X0
       have i₂ := eq14220
       grind)
    | exact superpose eq14220 eq14242
    | exact resolve eq14242 eq14220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14242
  have eq14428 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14229 X0
       have i₂ := eq14220
       grind)
    | exact superpose eq14220 eq14229
    | exact resolve eq14229 eq14220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14220 eq14229
  have eq15312 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14419 (σ y)
       grind)
    | exact superpose eq14419 eq16
    | exact resolve eq16 eq14419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14419
  have eq15359 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq15312
       have i₂ := eq14428 y
       grind)
    | exact superpose eq14428 eq15312
    | exact resolve eq15312 eq14428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14428 eq15312
  have eq15360 : False := by grind
  exact eq15360

/-- `Equation2588`: `x = (y ◇ ((z ◇ y) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_y_pyx_Equation2588 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2588 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2588.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) y)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq14 X0 x x
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
  have eq75 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  clear eq72
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq209 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq215 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ≠ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq51 eq13
    | (have j0 := eq13 X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))
       grind)
    | (have r₁ := eq13 X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))
       have r₂ := eq51 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq229 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq93 X0 X0
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq93 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq93 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1007 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq989 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1013 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1007 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1007 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1007 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq3644 : ∀ X0 : G, (σ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) ≠ (σ (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    intro X0
    first
    | exact superpose eq220 eq1013
    | (have j0 := eq1013 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) X0
       grind)
    | exact resolve eq1013 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq3659 : ∀ X0 : G, (σ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) ≠ (σ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    intro X0
    first
    | exact superpose eq51 eq3644
    | (have j0 := eq3644 X0
       grind)
    | exact resolve eq3644 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq3644
  have eq3660 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    intro X0
    first
    | (have j0 := eq3659 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3659
  have eq3825 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    first
    | exact superpose eq3660 eq37
    | exact resolve eq37 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq3826 : (M.op (σ x) (σ x)) = (σ (k x (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    first
    | exact superpose eq3660 eq35
    | exact resolve eq35 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3660
  have eq3851 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq220 eq3826
    | exact resolve eq3826 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3826
  have eq3852 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq220 eq3825
    | exact resolve eq3825 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq3825
  have eq3887 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3851
       grind)
    | exact superpose eq3851 eq16
    | exact resolve eq16 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3986 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3852 eq16
    | exact resolve eq16 eq3852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3852
  have eq26342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq26342
    | exact resolve eq26342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26342
  have eq26355 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq26343
       have r₂ := eq27
       grind)
    | exact resolve eq26343 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26343
  have eq26359 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq26355
    | exact resolve eq26355 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26355
  have eq26361 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26359 eq3887
    | exact resolve eq3887 eq26359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26359
  have eq26421 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq26361
    | exact resolve eq26361 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26361
  have eq26422 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26421
  have eq26602 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3851
       have i₂ := eq26422
       grind)
    | exact superpose eq26422 eq3851
    | exact resolve eq3851 eq26422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26610 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq26422
       grind)
    | exact superpose eq26422 eq52
    | exact resolve eq52 eq26422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26663 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26602
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26602
    | exact resolve eq26602 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26602
  have eq26674 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26663 eq52
    | exact resolve eq52 eq26663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26729 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26610 X0
       have i₂ := eq26422
       grind)
    | exact superpose eq26422 eq26610
    | exact resolve eq26610 eq26422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26422 eq26610
  have eq26878 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq26729 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26729
  have eq27102 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26878 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26878
    | (have j0 := eq26878 y
       grind)
    | exact resolve eq26878 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26878
  have eq27260 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27102 eq27
    | exact resolve eq27 eq27102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27262 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27102 eq76
    | (have r₁ := eq76
       have r₂ := eq27102
       grind)
    | exact resolve eq76 eq27102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27102
  have eq27271 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq27262
  have eq27939 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26663 eq26674
    | exact resolve eq26674 eq26663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26663 eq26674
  have eq28094 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq27939 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27939
  have eq28125 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq28094
    | (have j0 := eq28094 (σ y)
       grind)
    | exact resolve eq28094 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28094
  have eq28282 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28125 eq27
    | exact resolve eq27 eq28125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28125
  have eq59316 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27271 eq113
    | exact resolve eq113 eq27271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27271
  have eq59352 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq59316
  have eq59365 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq59352
       have r₂ := eq27260
       grind)
    | exact resolve eq59352 eq27260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27260 eq59352
  have eq101181 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq59365 eq3887
    | exact resolve eq3887 eq59365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59365
  have eq101365 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq101181
    | exact resolve eq101181 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101181
  have eq101366 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq101365
  have eq101399 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq101366
       grind)
    | exact superpose eq101366 eq52
    | exact resolve eq52 eq101366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq105685 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq101399 X0
       have i₂ := eq101366
       grind)
    | exact superpose eq101366 eq101399
    | exact resolve eq101399 eq101366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101366 eq101399
  have eq105950 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq105685 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105685
  have eq105986 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq105950 y
       grind)
    | exact superpose eq105950 eq18
    | (have j1 := eq105950 y
       grind)
    | exact resolve eq18 eq105950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105950
  have eq106224 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq105986
  have eq106286 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106224 eq20
    | exact resolve eq20 eq106224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106224
  have eq106476 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106286
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq106286
    | exact resolve eq106286 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106286
  have eq106518 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106476 eq26
    | exact resolve eq26 eq106476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106618 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106476 eq28282
    | (have r₁ := eq28282
       have r₂ := eq106476
       grind)
    | exact resolve eq28282 eq106476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28282 eq106476
  have eq106662 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq106618
  have eq106663 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq106662
  have eq106775 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106663 eq27
    | exact resolve eq27 eq106663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106777 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106663 eq76
    | (have r₁ := eq76
       have r₂ := eq106663
       grind)
    | exact resolve eq76 eq106663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq106778 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106663 eq215
    | exact resolve eq215 eq106663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq106818 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq106777
  have eq106836 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq106778
    | (have j0 := eq106778 X0
       grind)
    | exact resolve eq106778 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106778
  have eq109870 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106663 eq106836
    | exact resolve eq106836 eq106663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106663 eq106836
  have eq110142 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq109870 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109870
  have eq129288 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106818 eq113
    | exact resolve eq113 eq106818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq106818
  have eq129339 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq129288
  have eq129359 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq129339
       have r₂ := eq106775
       grind)
    | exact resolve eq129339 eq106775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106775 eq129339
  have eq132853 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129359 eq3887
    | exact resolve eq3887 eq129359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887 eq129359
  have eq133060 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq132853
    | exact resolve eq132853 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq132853
  have eq133061 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq133060
  have eq133066 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3851
       have i₂ := eq133061
       grind)
    | exact superpose eq133061 eq3851
    | exact resolve eq3851 eq133061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133061
  have eq133238 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133066
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq133066
    | exact resolve eq133066 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133066
  have eq133279 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq133238 eq110142
    | exact resolve eq110142 eq133238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110142 eq133238
  have eq133386 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq133279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133279
  have eq133460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq133386 eq106518
    | exact resolve eq106518 eq133386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106518 eq133386
  have eq133743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq133460
  have eq133803 : x = (M.op x y) := by
    first
    | (have r₁ := eq133743
       have r₂ := eq27
       grind)
    | exact resolve eq133743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133743
  have eq133812 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq133803 eq20
    | exact resolve eq20 eq133803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq133818 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq133803 eq75
    | (have r₁ := eq75
       have r₂ := eq133803
       grind)
    | exact resolve eq75 eq133803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq133859 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq133803 eq209
    | exact resolve eq209 eq133803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq133911 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq133818
  have eq133963 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq133859 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133859
    | (have j0 := eq133859 X0
       grind)
    | exact resolve eq133859 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133859
  have eq134009 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq133812
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq133812
    | exact resolve eq133812 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133812
  have eq134037 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq133803 eq133963
    | exact resolve eq133963 eq133803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133963
  have eq134075 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq134009 eq26
    | exact resolve eq26 eq134009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139310 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq997 x y
       have i₂ := eq133911
       grind)
    | exact superpose eq133911 eq997
    | (have j0 := eq997 x y
       grind)
    | exact resolve eq997 eq133911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997 eq133911
  have eq139313 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq139310
  have eq139320 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq139313
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq139313
    | exact resolve eq139313 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139313
  have eq139335 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq139320
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq139320
    | exact resolve eq139320 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139320
  have eq139349 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq139335
    | exact resolve eq139335 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq139335
  have eq139363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq134009 eq139349
    | exact resolve eq139349 eq134009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139349
  have eq139371 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq139363
       have r₂ := eq27
       grind)
    | exact resolve eq139363 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139363
  have eq139376 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq139371
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq139371
    | exact resolve eq139371 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139371
  have eq139381 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq134009 eq139376
    | exact resolve eq139376 eq134009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139376
  have eq141278 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq139381 eq3986
    | exact resolve eq3986 eq139381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3986 eq139381
  have eq141409 : (τ (σ (M.op x y))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq133803 eq141278
    | exact resolve eq141278 eq133803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141278
  have eq141433 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq141409
    | exact resolve eq141409 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq141409
  have eq141456 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq133803 eq141433
    | exact resolve eq141433 eq133803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141433
  have eq141457 : x = (M.op x x) := by grind
  clear eq141456
  have eq141485 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3851
       have i₂ := eq141457
       grind)
    | exact superpose eq141457 eq3851
    | exact resolve eq3851 eq141457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851
  have eq141520 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq134037 X0
       have i₂ := eq141457
       grind)
    | exact superpose eq141457 eq134037
    | exact resolve eq134037 eq141457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134037 eq141457
  have eq141662 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134009 eq141485
    | exact resolve eq141485 eq134009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141485
  have eq141692 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq141662
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq141662
    | exact resolve eq141662 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141662
  have eq141707 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134009 eq141692
    | exact resolve eq141692 eq134009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141692
  have eq142411 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq141520 y
       grind)
    | exact superpose eq141520 eq18
    | (have j1 := eq141520 y
       grind)
    | exact resolve eq18 eq141520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq141520
  have eq142736 : x = y := by
    first
    | exact superpose eq133803 eq142411
    | exact resolve eq142411 eq133803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133803 eq142411
  have eq142780 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq142736
       grind)
    | exact superpose eq142736 eq24
    | exact resolve eq24 eq142736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq142736
  have eq143053 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq142780
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq142780
    | exact resolve eq142780 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq142780
  have eq143146 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq134009 eq143053
    | exact resolve eq143053 eq134009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134009 eq143053
  have eq143776 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq141707 eq229
    | exact resolve eq229 eq141707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq143909 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq141707 eq143776
    | exact resolve eq143776 eq141707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141707 eq143776
  have eq145393 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq143909 eq134075
    | exact resolve eq134075 eq143909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134075 eq143909
  have eq145687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq143146 eq145393
    | exact resolve eq145393 eq143146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143146 eq145393
  have eq145741 : False := by grind
  exact eq145741

/-- `Equation2588`: `x = (y ◇ ((z ◇ y) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pyx_Equation2588 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2588 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2588.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X0) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq55 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq14 X0 x x
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
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 (M.op x x) x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq420 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq55
    | exact resolve eq55 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq420 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq55 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq55 eq420
    | exact resolve eq420 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq1065 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1014 X0 X1
       have i₂ := eq45 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq45 eq1014
    | exact resolve eq1014 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1014
  have eq1085 : ∀ X0 X1 : G, (M.op (σ (M.op X0 (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1065 X0 X1
       have i₂ := eq55 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have i₁ := eq1065 X0 X1
       have i₂ := eq55 X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq55 eq1065
    | exact resolve eq1065 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq34741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (M.op (σ x) (σ x)) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq34742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq34741
    | exact resolve eq34741 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34741
  have eq34753 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq34742
       have r₂ := eq28
       grind)
    | exact resolve eq34742 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34742
  have eq35468 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq34753 eq69
    | exact resolve eq69 eq34753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34753
  have eq35555 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq35468
    | exact resolve eq35468 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35468
  have eq35556 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq35555
  have eq35564 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq35556
       grind)
    | exact superpose eq35556 eq52
    | exact resolve eq52 eq35556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35572 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq35556
       grind)
    | exact superpose eq35556 eq55
    | exact resolve eq55 eq35556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq35591 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1085 x X0
       have i₂ := eq35556
       grind)
    | exact superpose eq35556 eq1085
    | exact resolve eq1085 eq35556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq35640 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35591 X0
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq35591
    | exact resolve eq35591 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq35591
  have eq35652 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq35564
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35564
    | exact resolve eq35564 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35564
  have eq35756 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35572 X0
       have i₂ := eq35556
       grind)
    | exact superpose eq35556 eq35572
    | exact resolve eq35572 eq35556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35556 eq35572
  have eq35929 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq35756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35756
  have eq35961 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq35929 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35929
    | (have j0 := eq35929 y
       grind)
    | exact resolve eq35929 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35929
  have eq36153 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq35961 eq30
    | exact resolve eq30 eq35961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35961
  have eq36273 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq36153
    | exact resolve eq36153 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36153
  have eq36274 : y = (M.op x y) ∨ x = y := by grind
  clear eq36273
  have eq37140 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq36274 eq21
    | exact resolve eq21 eq36274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36274
  have eq37257 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq37140
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37140
    | exact resolve eq37140 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37140
  have eq37273 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq37257 eq27
    | exact resolve eq27 eq37257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37257
  have eq51389 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq35652 eq35640
    | exact resolve eq35640 eq35652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35640 eq35652
  have eq51576 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq51389 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51389
  have eq51615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq51576 eq37273
    | exact resolve eq37273 eq51576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37273 eq51576
  have eq51772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51615
  have eq51813 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq51772
       have r₂ := eq28
       grind)
    | exact resolve eq51772 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51772
  have eq51829 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq51813 eq30
    | exact resolve eq30 eq51813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq51813
  have eq52050 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq51829
    | exact resolve eq51829 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq51829
  have eq52051 : x = y := by grind
  clear eq52050
  have eq52070 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq52051
       grind)
    | exact superpose eq52051 eq19
    | exact resolve eq19 eq52051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq52071 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq52051
       grind)
    | exact superpose eq52051 eq25
    | exact resolve eq25 eq52051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq52051
  have eq52208 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq52071
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52071
    | exact resolve eq52071 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq52071
  have eq52228 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq52208 eq27
    | exact resolve eq27 eq52208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq52208
  have eq52563 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq52228 eq69
    | exact resolve eq69 eq52228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq52228
  have eq52648 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52563
       have i₂ := eq52070
       grind)
    | exact superpose eq52070 eq52563
    | exact resolve eq52563 eq52070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52070 eq52563
  have eq52657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52648 eq15
    | exact resolve eq15 eq52648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52648
  have eq52736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq52657
    | exact resolve eq52657 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq52657
  have eq52757 : False := by grind
  exact eq52757
