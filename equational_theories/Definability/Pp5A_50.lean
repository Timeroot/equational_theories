import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq178 X0 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq594 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq594
    | exact resolve eq594 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq594
  have eq644 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq721 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq721 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq721 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq721 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq721 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq721 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq739 : ∀ X0 : G, (M.op X0 (k (k X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq604 X0
       have i₂ := eq726 X0
       grind)
    | exact superpose eq726 eq604
    | exact resolve eq604 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq831 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq644
       grind)
    | exact superpose eq644 eq40
    | exact resolve eq40 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq832 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq831
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq831
    | exact resolve eq831 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq834 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq832
    | exact resolve eq832 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq834 eq649
    | exact resolve eq649 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq842
       have r₂ := eq27
       grind)
    | exact resolve eq842 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq854 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq849 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq849
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq849
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq849
       grind)
    | exact resolve eq12 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq864 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq854
       have r₂ := eq26
       grind)
    | exact resolve eq854 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq868 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq864
       have i₂ := eq726 sF2
       grind)
    | exact superpose eq726 eq864
    | exact resolve eq864 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq870 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq834 eq868
    | exact resolve eq868 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq868
  have eq871 : (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq870
       have r₂ := eq27
       grind)
    | exact resolve eq870 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq872 : (τ (σ y)) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq871 eq98
    | exact resolve eq98 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq881 : (M.op x y) = (M.op y x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq872
    | exact resolve eq872 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq895 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq881
       grind)
    | exact superpose eq881 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq881
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq881
       grind)
    | exact resolve eq12 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq905 : y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have r₁ := eq895
       have r₂ := eq18
       grind)
    | exact resolve eq895 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq908 : y = (k x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq905
       have i₂ := eq726 x
       grind)
    | exact superpose eq726 eq905
    | exact resolve eq905 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq909 : (M.op x y) = (k y x) ∨ y = (k x x) := by grind
  clear eq908
  have eq931 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq40
    | exact resolve eq40 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq932 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq931
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq931
    | exact resolve eq931 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq934 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq20 eq932
    | exact resolve eq932 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq934 eq649
    | exact resolve eq649 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq953 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq946
       have r₂ := eq27
       grind)
    | exact resolve eq946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq958 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq953 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq953
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq953
       grind)
    | exact resolve eq12 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq968 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq958
       have r₂ := eq26
       grind)
    | exact resolve eq958 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq972 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq968
       have i₂ := eq726 sF2
       grind)
    | exact superpose eq726 eq968
    | exact resolve eq968 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq974 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq934 eq972
    | exact resolve eq972 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934 eq972
  have eq975 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq974
       have r₂ := eq27
       grind)
    | exact resolve eq974 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq976 : (τ (σ y)) = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq975 eq98
    | exact resolve eq98 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq975
  have eq985 : y = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq976
    | exact resolve eq976 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq976
  have eq986 : y = (k x x) := by grind
  clear eq985
  have eq992 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq986
       grind)
    | exact superpose eq986 eq40
    | exact resolve eq40 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq993 : x = (M.op x (k y x)) := by
    first
    | (have i₁ := eq739 x
       have i₂ := eq986
       grind)
    | exact superpose eq986 eq739
    | exact resolve eq739 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq992
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq992
    | exact resolve eq992 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq992
  have eq998 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq996
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq996
    | exact resolve eq996 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1003 : (σ x) = (M.op (σ x) (k (σ y) (σ x))) := by
    first
    | exact superpose eq998 eq739
    | exact resolve eq739 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq1015 : (M.op x x) = (M.op (k y x) x) := by
    first
    | (have i₁ := eq178 x (k y x)
       have i₂ := eq993
       grind)
    | exact superpose eq993 eq178
    | exact resolve eq178 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1020 : (k x x) = (M.op (k y x) x) := by
    first
    | (have i₁ := eq1015
       have i₂ := eq726 x
       grind)
    | exact superpose eq726 eq1015
    | exact resolve eq1015 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1022 : y = (M.op (k y x) x) := by
    first
    | (have i₁ := eq1020
       have i₂ := eq986
       grind)
    | exact superpose eq986 eq1020
    | exact resolve eq1020 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq1020
  have eq1052 : (M.op (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq1003 eq178
    | exact resolve eq178 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1057 : (k (σ x) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq1052
       have i₂ := eq726 sF2
       grind)
    | exact superpose eq726 eq1052
    | exact resolve eq1052 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1059 : (σ y) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq998 eq1057
    | exact resolve eq1057 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998 eq1057
  have eq1089 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq178 (k y x) x
       have i₂ := eq1022
       grind)
    | exact superpose eq1022 eq178
    | exact resolve eq178 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1094 : (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq1089
       have i₂ := eq726 y
       grind)
    | exact superpose eq726 eq1089
    | exact resolve eq1089 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1099 : (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq1094
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1094
    | exact resolve eq1094 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1094
  have eq1433 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1099
       grind)
    | exact superpose eq1099 eq41
    | exact resolve eq41 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1099
  have eq1438 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1433
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1433
    | exact resolve eq1433 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1433
  have eq1440 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq1438
    | exact resolve eq1438 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1438
  have eq1529 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1059 eq178
    | exact resolve eq178 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1059
  have eq1534 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1529
       have i₂ := eq726 sF3
       grind)
    | exact superpose eq726 eq1529
    | exact resolve eq1529 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq1529
  have eq1541 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1440 eq1534
    | exact resolve eq1534 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440 eq1534
  have eq1550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1541 eq26
    | exact resolve eq26 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1541
  have eq1561 : False := by grind
  exact eq1561

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq42
    | (have j0 := eq42 (σ X0) (σ X1)
       grind)
    | exact resolve eq42 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (k X2 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 X2 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq24 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X1 X1) X1 X2 X1
       have i₂ := eq25 X1 X1
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq24 X0 x x X3
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq16
    | (have j1 := eq55 y x
       grind)
    | exact resolve eq16 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (k X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq9
    | (have j1 := eq55 X0 X0
       grind)
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq342 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq156
       have i₂ := eq42 y x
       grind)
    | exact superpose eq42 eq156
    | (have j1 := eq42 (σ y) (σ x)
       grind)
    | exact resolve eq156 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq156
  have eq345 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq342
  have eq352 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq25 y y
       have i₂ := eq345
       grind)
    | exact superpose eq345 eq25
    | exact resolve eq25 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       have i₂ := eq114 (M.op X0 X0) x
       grind)
    | exact superpose eq114 eq9
    | exact resolve eq9 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq374 X0
       have i₂ := eq25 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq25 eq374
    | exact resolve eq374 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq384 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq381 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq381
    | exact resolve eq381 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq596 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq98 X0 X0 X0
       grind)
    | exact superpose eq98 eq98
    | exact resolve eq98 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq98 X0 X0 X0
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq817 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq81 X0 X0 (M.op X0 X0) (M.op x x)
       have i₂ := eq24 X0 x x X0
       grind)
    | exact superpose eq24 eq81
    | exact resolve eq81 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq81
  have eq1649 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (M.op (M.op X2 X1) (σ (k (τ X0) (τ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq164 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq164
    | exact resolve eq164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq1691 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 (σ (τ X0))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1649 X0 X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1649
    | (have j0 := eq1649 X0 X1 X2
       grind)
    | exact resolve eq1649 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1649
  have eq1692 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1691 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1691
    | (have j0 := eq1691 X0 X1 X2
       grind)
    | exact resolve eq1691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1719 : ∀ X0 : G, (M.op (M.op (k X0 X0) (k X0 X0)) (M.op (k X0 X0) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1692 X0 (M.op (k X0 X0) (k X0 X0)) x
       have i₂ := eq114 (k X0 X0) x
       grind)
    | exact superpose eq114 eq1692
    | (have j0 := eq1692 X0 x x
       grind)
    | exact resolve eq1692 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq1747 : ∀ X0 : G, (M.op (k X0 X0) (M.op (k X0 X0) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1719 X0
       have i₂ := eq25 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq25 eq1719
    | (have j0 := eq1719 X0
       grind)
    | exact resolve eq1719 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq5772 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109 (k X0 X0) X1 X2
       have i₂ := eq1747 X0
       grind)
    | exact superpose eq1747 eq109
    | (have j1 := eq1747 X0
       grind)
    | exact resolve eq109 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747
  have eq5899 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0
       have i₂ := eq5772 X0 X1 X2
       grind)
    | exact superpose eq5772 eq77
    | (have j1 := eq5772 X0 X1 X2
       grind)
    | exact resolve eq77 eq5772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5772
  have eq6855 : y = (M.op x (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq384 y
       have i₂ := eq345
       grind)
    | exact superpose eq345 eq384
    | exact resolve eq384 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq384
  have eq6936 : y = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6855
       have i₂ := eq352
       grind)
    | exact superpose eq352 eq6855
    | exact resolve eq6855 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq6855
  have eq6972 : y = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq6936
  have eq6979 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq109 x X1 x
       have i₂ := eq6972
       grind)
    | exact superpose eq6972 eq109
    | exact resolve eq109 eq6972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq6972
  have eq7063 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq817 (σ y)
       have i₂ := eq6979 X0 X1
       grind)
    | exact superpose eq6979 eq817
    | (have j1 := eq6979 X0 X1
       grind)
    | exact resolve eq817 eq6979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7745 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq7063 X0 X1
       grind)
    | exact superpose eq7063 eq16
    | (have j1 := eq7063 X0 X1
       grind)
    | exact resolve eq16 eq7063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7063
  have eq12315 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq106 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq620 X0 X0 X1
       grind)
    | exact superpose eq620 eq106
    | exact resolve eq106 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12406 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12315 X0 X1 x x x
       have i₂ := eq106 X0 X0 x x x
       grind)
    | exact superpose eq106 eq12315
    | exact resolve eq12315 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq12315
  have eq28661 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5899 X0 x x
       have i₂ := eq12406 X0 (M.op x x)
       grind)
    | exact superpose eq12406 eq5899
    | (have j0 := eq5899 X0 x x
       grind)
    | exact resolve eq5899 eq12406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5899
  have eq29189 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X1 X0
       have i₂ := eq28661 (M.op X0 X1)
       grind)
    | exact superpose eq28661 eq9
    | (have j1 := eq28661 (M.op X0 X1)
       grind)
    | exact resolve eq9 eq28661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28661
  have eq29257 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq29189 X0 X1
       have j1 := eq80 X1 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq29189 X1 X0
       have r₂ := eq80 X0 X1 x
       grind)
    | exact resolve eq29189 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq29189
  have eq29326 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29257 X0 X1
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq29257
    | exact resolve eq29257 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29257
  have eq29681 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29326 (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op x x))
       have i₂ := eq596 X0 X1 x
       grind)
    | exact superpose eq596 eq29326
    | exact resolve eq29326 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq29326
  have eq29832 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq29681 X0 x
       have i₂ := eq114 X0 (M.op x (M.op x x))
       grind)
    | exact superpose eq114 eq29681
    | exact resolve eq29681 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq29681
  have eq30219 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq29832 (σ X0)
       grind)
    | exact superpose eq29832 eq15
    | exact resolve eq15 eq29832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30235 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq29832 (τ X0)
       grind)
    | exact superpose eq29832 eq34
    | exact resolve eq34 eq29832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq30299 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30235 X0
       have i₂ := eq29832 X0
       grind)
    | exact superpose eq29832 eq30235
    | exact resolve eq30235 eq29832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30235
  have eq30315 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30219 X0
       have i₂ := eq29832 X0
       grind)
    | exact superpose eq29832 eq30219
    | exact resolve eq30219 eq29832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29832 eq30219
  have eq33405 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq817 (τ X0)
       have i₂ := eq30299 X0
       grind)
    | exact superpose eq30299 eq817
    | exact resolve eq817 eq30299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30299
  have eq35245 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ x = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq33405 (σ y)
       have i₂ := eq6979 X0 X1
       grind)
    | exact superpose eq6979 eq33405
    | (have j1 := eq6979 X0 X1
       grind)
    | exact resolve eq33405 eq6979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6979 eq33405
  have eq35386 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq35245 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq35245
    | (have j0 := eq35245 X0 X1
       grind)
    | exact resolve eq35245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35245
  have eq35416 : ∀ X0 X1 : G, x = (M.op x y) ∨ x = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq35386 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35386
    | (have j0 := eq35386 X0 X1
       grind)
    | exact resolve eq35386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35386
  have eq35432 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq35416 x x
       have i₂ := eq12406 y (M.op x x)
       grind)
    | exact superpose eq12406 eq35416
    | exact resolve eq35416 eq12406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35416
  have eq35447 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ x = (M.op (M.op (M.op X0 X1) y) y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq7745 X0 X1
       have i₂ := eq35432
       grind)
    | exact superpose eq35432 eq7745
    | (have j0 := eq7745 X0 X1
       grind)
    | exact resolve eq7745 eq35432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7745 eq35432
  have eq35495 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) y) y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq35447 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35447
  have eq35512 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq35495 x x
       have i₂ := eq12406 y (M.op x x)
       grind)
    | exact superpose eq12406 eq35495
    | exact resolve eq35495 eq12406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12406 eq35495
  have eq35513 : x = (M.op y y) := by grind
  clear eq35512
  have eq35558 : x = (M.op x y) := by
    first
    | (have i₁ := eq817 y
       have i₂ := eq35513
       grind)
    | exact superpose eq35513 eq817
    | exact resolve eq817 eq35513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq35591 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq35513
       grind)
    | exact superpose eq35513 eq9
    | exact resolve eq9 eq35513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35619 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq620 X0 y y
       have i₂ := eq35513
       grind)
    | exact superpose eq35513 eq620
    | exact resolve eq620 eq35513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq39298 : ∀ X0 : G, (σ X0) = (M.op y (M.op x (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq35591 (σ X0)
       have i₂ := eq30315 X0
       grind)
    | exact superpose eq30315 eq35591
    | exact resolve eq35591 eq30315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30315 eq35591
  have eq71230 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq35619 X0
       grind)
    | exact superpose eq35619 eq77
    | exact resolve eq77 eq35619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq35619
  have eq84952 : (σ y) = (M.op y (M.op x (σ x))) := by
    first
    | (have i₁ := eq39298 y
       have i₂ := eq35513
       grind)
    | exact superpose eq35513 eq39298
    | exact resolve eq39298 eq35513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35513 eq39298
  have eq85724 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71230 (σ x)
       have i₂ := eq84952
       grind)
    | exact superpose eq84952 eq71230
    | exact resolve eq71230 eq84952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71230 eq84952
  have eq85924 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85724
       grind)
    | exact superpose eq85724 eq16
    | exact resolve eq16 eq85724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85724
  have eq86020 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq85924
       have i₂ := eq35558
       grind)
    | exact superpose eq35558 eq85924
    | exact resolve eq85924 eq35558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35558 eq85924
  have eq86021 : False := by grind
  exact eq86021

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq92 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq88
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq219 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq54 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq55 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (M.op X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 (σ X0) X1 X2 X3
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq55
    | exact resolve eq55 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq56 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq55 X0 x x X3
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq55 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq55 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq766 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq763 X0 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq763
    | exact resolve eq763 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq767 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq762
    | exact resolve eq762 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq762
  have eq1036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1037 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1036
    | exact resolve eq1036 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1040 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1037
       have r₂ := eq28
       grind)
    | exact resolve eq1037 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1042 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1040
    | exact resolve eq1040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1045 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1042 eq54
    | exact resolve eq54 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1770 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X0))
       have i₂ := eq722 X0 X0 X0
       grind)
    | exact superpose eq722 eq53
    | exact resolve eq53 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1771 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 (M.op X0 X0))
       have i₂ := eq722 X0 X0 X0
       grind)
    | exact superpose eq722 eq54
    | exact resolve eq54 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq4236 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq496 X0 X0 (M.op X0 X0) x
       have i₂ := eq722 x X0 X0
       grind)
    | exact superpose eq722 eq496
    | exact resolve eq496 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq4474 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq496 (σ X0) (σ X0) (σ (M.op X0 X0)) (M.op x x)
       have i₂ := eq741 X0 x x (σ X0)
       grind)
    | exact superpose eq741 eq496
    | exact resolve eq496 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq741
  have eq4490 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4474 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq4474
    | exact resolve eq4474 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4474
  have eq5263 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq767 X0 X1
       have i₂ := eq766 X0 X1
       grind)
    | exact superpose eq766 eq767
    | exact resolve eq767 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq767
  have eq5608 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq5263
    | (have j0 := eq5263 (σ x) (σ y)
       grind)
    | exact resolve eq5263 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5263
  have eq5682 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq219 eq5608
    | exact resolve eq5608 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq5608
  have eq16483 : (σ x) = (M.op (σ y) (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1045 sF2
       have i₂ := eq1770 sF2
       grind)
    | exact superpose eq1770 eq1045
    | exact resolve eq1045 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq16738 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1042 eq1771
    | exact resolve eq1771 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771
  have eq28748 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq492 X0
       have i₂ := eq16738 X0
       grind)
    | exact superpose eq16738 eq492
    | exact resolve eq492 eq16738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16738
  have eq29072 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq28748
    | (have j0 := eq28748 (σ y)
       grind)
    | exact resolve eq28748 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28748
  have eq29209 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq5682 eq29072
    | exact resolve eq29072 eq5682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5682 eq29072
  have eq29562 : (σ y) = (M.op y (M.op (M.op x y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1042 eq29209
    | exact resolve eq29209 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq29209
  have eq29609 : (σ y) = (M.op y (M.op (M.op x y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq29562
  have eq29856 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29609 eq16483
    | exact resolve eq16483 eq29609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16483 eq29609
  have eq29903 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq29856
  have eq29965 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29903 eq127
    | exact resolve eq127 eq29903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq29903
  have eq30067 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq29965
    | exact resolve eq29965 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29965
  have eq30648 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4236 y
       have i₂ := eq30067
       grind)
    | exact superpose eq30067 eq4236
    | exact resolve eq4236 eq30067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4236 eq30067
  have eq30706 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq30648
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30648
    | exact resolve eq30648 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30648
  have eq30707 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq30706
  have eq30739 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30707 eq30
    | exact resolve eq30 eq30707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq30707
  have eq30785 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq30739
    | exact resolve eq30739 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq30739
  have eq30786 : x = (M.op x y) ∨ x = y := by grind
  clear eq30785
  have eq30852 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30786 eq21
    | exact resolve eq21 eq30786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30924 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30786 eq1770
    | exact resolve eq1770 eq30786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770 eq30786
  have eq31015 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq30852
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30852
    | exact resolve eq30852 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30852
  have eq31030 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq31015 eq27
    | exact resolve eq27 eq31015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31015
  have eq58403 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq492 X0
       have i₂ := eq30924 X0
       grind)
    | exact superpose eq30924 eq492
    | exact resolve eq492 eq30924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq30924
  have eq58752 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 X1) (M.op y y)) y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq747 y x X0 X1 y
       have i₂ := eq58403 y
       grind)
    | exact superpose eq58403 eq747
    | exact resolve eq747 eq58403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq58403
  have eq58872 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq58752 x x
       have i₂ := eq758 y (M.op x x)
       grind)
    | exact superpose eq758 eq58752
    | exact resolve eq58752 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758 eq58752
  have eq58874 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq58872
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58872
    | exact resolve eq58872 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58872
  have eq58948 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4490 y
       have i₂ := eq58874
       grind)
    | exact superpose eq58874 eq4490
    | exact resolve eq4490 eq58874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4490 eq58874
  have eq59020 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq58948
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq58948
    | exact resolve eq58948 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58948
  have eq59054 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq59020
    | exact resolve eq59020 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59020
  have eq59303 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq59054 eq31030
    | exact resolve eq31030 eq59054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31030 eq59054
  have eq59352 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq59303
  have eq59360 : x = y := by
    first
    | (have r₁ := eq59352
       have r₂ := eq28
       grind)
    | exact resolve eq59352 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59352
  have eq59376 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq59360
       grind)
    | exact superpose eq59360 eq19
    | exact resolve eq19 eq59360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq59377 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq59360
       grind)
    | exact superpose eq59360 eq25
    | exact resolve eq25 eq59360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq59360
  have eq59540 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq59377
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq59377
    | exact resolve eq59377 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq59377
  have eq59566 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq59540 eq27
    | exact resolve eq27 eq59540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq59540
  have eq59970 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq59566 eq68
    | exact resolve eq68 eq59566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq59566
  have eq60140 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq59970
       have i₂ := eq59376
       grind)
    | exact superpose eq59376 eq59970
    | exact resolve eq59970 eq59376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59376 eq59970
  have eq60220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60140 eq15
    | exact resolve eq15 eq60140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60140
  have eq60299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq60220
    | exact resolve eq60220 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq60220
  have eq60324 : False := by grind
  exact eq60324

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxx_x_pxy_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq49
    | exact resolve eq49 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq72
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq72
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq70
    | exact resolve eq70 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op y y) = (M.op y x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op y y) = (M.op y x) := by
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
  have eq97 : (M.op y y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq68 sF3
       grind)
    | exact superpose eq68 eq104
    | exact resolve eq104 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq68 y
       grind)
    | exact superpose eq68 eq108
    | exact resolve eq108 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq145 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq10
    | exact resolve eq10 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq14
    | exact resolve eq14 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq789 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 x
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq238 eq50
    | exact resolve eq50 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op X2 y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq904 eq55
    | exact resolve eq55 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq927 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq925 X0 X1 x
       have i₂ := eq14 (M.op sF0 X0) y x
       grind)
    | exact superpose eq14 eq925
    | exact resolve eq925 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq969 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq244 eq51
    | exact resolve eq51 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq969 eq55
    | exact resolve eq55 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1088 X0 X1 x
       have i₂ := eq14 (M.op sF4 X0) sF3 x
       grind)
    | exact superpose eq14 eq1088
    | exact resolve eq1088 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq4581 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op X0 (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq244 eq249
    | exact resolve eq249 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq11473 : (σ (k (M.op y y) (M.op y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq145 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq145
    | exact resolve eq145 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq145
  have eq11572 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq11473
       have i₂ := eq68 (M.op sF3 sF3)
       grind)
    | exact superpose eq68 eq11473
    | exact resolve eq11473 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11473
  have eq11580 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq11572
       have i₂ := eq68 (M.op y y)
       grind)
    | exact superpose eq68 eq11572
    | exact resolve eq11572 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq11572
  have eq11584 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1090 eq11580
    | exact resolve eq11580 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq11580
  have eq11587 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq244 eq11584
    | exact resolve eq11584 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq11584
  have eq11588 : (σ (M.op (M.op x y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq11587
       have i₂ := eq927 (M.op y y) y
       grind)
    | exact superpose eq927 eq11587
    | exact resolve eq11587 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq11587
  have eq11589 : (σ (M.op y (M.op (M.op x y) y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq238 eq11588
    | exact resolve eq11588 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq11588
  have eq11592 : (M.op y (M.op (M.op x y) y)) = (τ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq11589 eq16
    | exact resolve eq16 eq11589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68637 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq503 X0 (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq503
    | exact resolve eq503 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq68781 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq68637 X0
       have i₂ := eq75 (M.op X0 X0)
       grind)
    | exact superpose eq75 eq68637
    | exact resolve eq68637 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq68637
  have eq77614 : (σ x) = (M.op (σ x) (σ (M.op (M.op x x) (M.op x x)))) := by
    first
    | (have i₁ := eq68781 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq68781
    | (have j0 := eq68781 x
       grind)
    | exact resolve eq68781 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68781
  have eq78061 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x (M.op (M.op X0 x) x)))) := by
    intro X0
    first
    | (have i₁ := eq77614
       have i₂ := eq55 x x X0 x
       grind)
    | exact superpose eq55 eq77614
    | exact resolve eq77614 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq77614
  have eq105639 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq14
    | exact resolve eq14 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq105829 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq105639 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq105639
    | exact resolve eq105639 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105639
  have eq105968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq105829 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq105829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105829
  have eq105981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq105968
    | exact resolve eq105968 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105968
  have eq105994 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq105981
       have r₂ := eq27
       grind)
    | exact resolve eq105981 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105981
  have eq106043 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq105994 eq14
    | exact resolve eq14 eq105994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105994
  have eq106233 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq106043 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq106043
    | exact resolve eq106043 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106043
  have eq106362 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq106233 eq51
    | exact resolve eq51 eq106233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq106233
  have eq107514 : (τ (σ x)) = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq106362 eq11592
    | exact resolve eq11592 eq106362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11592 eq106362
  have eq107755 : x = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq107514
    | exact resolve eq107514 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107514
  have eq110436 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq107755 eq904
    | exact resolve eq904 eq107755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq107755
  have eq110572 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110436
  have eq110795 : x = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq110572
       grind)
    | exact superpose eq110572 eq50
    | exact resolve eq50 eq110572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq110859 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq789 x y X0
       have i₂ := eq110572
       grind)
    | exact superpose eq110572 eq789
    | exact resolve eq789 eq110572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq111035 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq110795 eq11589
    | exact resolve eq11589 eq110795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11589 eq110795
  have eq111286 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq111035
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq111035
    | exact resolve eq111035 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111035
  have eq112836 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq111286 eq969
    | exact resolve eq969 eq111286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq112839 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq111286 eq4581
    | exact resolve eq4581 eq111286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4581 eq111286
  have eq119252 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110859 x
       have i₂ := eq110572
       grind)
    | exact superpose eq110572 eq110859
    | exact resolve eq110859 eq110572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110572 eq110859
  have eq119390 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq119252
  have eq119446 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq119390
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119390
    | exact resolve eq119390 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119390
  have eq119481 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq119446 eq787
    | exact resolve eq787 eq119446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq119446
  have eq119737 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq78061 x
       have i₂ := eq119481 x
       grind)
    | exact superpose eq119481 eq78061
    | exact resolve eq78061 eq119481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78061 eq119481
  have eq119993 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq119737
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119737
    | exact resolve eq119737 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119737
  have eq120029 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq119993
    | exact resolve eq119993 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119993
  have eq140244 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq120029 eq112839
    | exact resolve eq112839 eq120029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112839 eq120029
  have eq140389 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq140244
  have eq140473 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq112836 eq140389
    | exact resolve eq140389 eq112836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112836 eq140389
  have eq140605 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq140473
  have eq140670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq140605
    | exact resolve eq140605 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140605
  have eq140692 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq140670
       have r₂ := eq27
       grind)
    | exact resolve eq140670 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140670
  have eq140697 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq140692 eq29
    | exact resolve eq29 eq140692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq140692
  have eq140872 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq140697
    | exact resolve eq140697 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq140697
  have eq140873 : x = y := by grind
  clear eq140872
  have eq140892 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq140873
       grind)
    | exact superpose eq140873 eq18
    | exact resolve eq18 eq140873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq140893 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq140873
       grind)
    | exact superpose eq140873 eq24
    | exact resolve eq24 eq140873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq140873
  have eq141087 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq140893
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140893
    | exact resolve eq140893 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq140893
  have eq141108 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq141087 eq26
    | exact resolve eq26 eq141087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq141087
  have eq141629 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq141108 eq73
    | exact resolve eq73 eq141108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq141108
  have eq141880 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq141629
       have i₂ := eq140892
       grind)
    | exact superpose eq140892 eq141629
    | exact resolve eq141629 eq140892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140892 eq141629
  have eq141924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141880 eq15
    | exact resolve eq15 eq141880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141880
  have eq142023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq141924
    | exact resolve eq141924 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq141924
  have eq142050 : False := by grind
  exact eq142050

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op X1 X0) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44
    | (have j0 := eq44 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq44 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq19
    | exact resolve eq19 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq83
    | exact resolve eq83 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq135 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq255 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq135
       have i₂ := eq44 y x
       grind)
    | exact superpose eq44 eq135
    | (have j1 := eq44 (σ x) (σ y)
       grind)
    | (have r₁ := eq135
       have r₂ := eq44 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq135
       have r₂ := eq44 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq135 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq135
  have eq256 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq255
  have eq257 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256
       grind)
    | exact superpose eq256 eq16
    | exact resolve eq16 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq258 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq257
       have r₂ := eq95 x
       grind)
    | exact resolve eq257 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq289 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq258
       grind)
    | exact superpose eq258 eq10
    | exact resolve eq10 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq308 : x = y := by
    first
    | (have i₁ := eq289
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq289
    | exact resolve eq289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq347 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq308
       grind)
    | exact superpose eq308 eq16
    | exact resolve eq16 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq348 : False := by grind
  exact eq348

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X4 (M.op (M.op X2 X1) (M.op X1 X0))) X3)) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 (M.op (M.op X2 X1) (M.op X1 X0)) X4 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X2) (M.op (M.op X5 (M.op X0 X2)) X4)) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 X2) X4)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq52 X4 (M.op X0 X2) X5 (M.op x X0)
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X3 X2) (M.op X2 X0)))) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X3 X2) (M.op X2 X0)) X2 X4 X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X2 X0) X2 x X1
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq77 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq52 X2 X1 X4 X0
       grind)
    | exact superpose eq52 eq77
    | exact resolve eq77 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq77 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq77 X0 X2 X3
       grind)
    | exact superpose eq77 eq77
    | exact resolve eq77 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X2 X0)) (M.op X1 X2) X3
       have i₂ := eq77 X0 X1 X2
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq92 x X1 X2 X4 X3
       have i₂ := eq9 X2 X1 x
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq130 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq130 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq130 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq130 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq134 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq131 (σ X0)
       grind)
    | exact superpose eq131 eq15
    | exact resolve eq15 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq131 (τ X0)
       grind)
    | exact superpose eq131 eq18
    | exact resolve eq18 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq138 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq138
    | exact resolve eq138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq145 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq134 X0
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq134
    | exact resolve eq134 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq149 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq141 X0
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq141
    | exact resolve eq141 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq141
  have eq155 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq9
    | exact resolve eq9 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) = (M.op (σ X0) (M.op (M.op X2 (σ X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (σ X0) X2 (σ X0)
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq52
    | exact resolve eq52 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq231 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0)) = (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X3 X1 X2 (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0))
       have i₂ := eq51 X3 X1 X2 X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op (M.op X1 X2) (M.op X2 X3))) X4) = (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 X3))) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq51 X3 X1 X2 (M.op (M.op X5 (M.op (M.op X1 X2) (M.op X2 X3))) X4)
       have i₂ := eq52 X4 (M.op (M.op X1 X2) (M.op X2 X3)) X5 X0
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq248 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op (M.op X2 X1) (M.op X1 X0))) X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq104 (M.op (M.op X2 X1) (M.op X1 X0)) X3 X1 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq104
    | exact resolve eq104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 (σ X0) X1 (σ X0) X2
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq104
    | exact resolve eq104 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq155 X0 (σ X0)
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq155
    | exact resolve eq155 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq650 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq632 X0
       have i₂ := eq145 (M.op X0 X0)
       grind)
    | exact superpose eq145 eq632
    | exact resolve eq632 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq801 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq181 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq181 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq181 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq181 X0 X1
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq815 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq801 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq816 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq815 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq820 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq816 X0 X1
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq816
    | (have j0 := eq816 X0 X1
       grind)
    | exact resolve eq816 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq830 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq820 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq820
    | (have j0 := eq820 X0 X1
       grind)
    | exact resolve eq820 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq987 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0
       have i₂ := eq52 X0 X0 X1 X0
       grind)
    | exact superpose eq52 eq650
    | exact resolve eq650 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq650
  have eq9731 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 X2) X4)) = (M.op X2 (M.op X2 X4)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq66 X0 X1 X2 X4 x
       have i₂ := eq99 X4 X0 X2 x
       grind)
    | exact superpose eq99 eq66
    | exact resolve eq66 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq10378 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq987 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq9731 X0 X0 X0 X0
       grind)
    | exact superpose eq9731 eq987
    | exact resolve eq987 eq9731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10397 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X0 X1)) X5) = (M.op (M.op (M.op X2 X0) X1) (M.op (M.op X3 (M.op (M.op X2 X0) X1)) (M.op (M.op X4 (M.op (M.op X2 X0) X1)) (M.op (M.op (M.op X2 X0) X1) X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq67 X5 (M.op X2 (M.op (M.op x X2) X0)) (M.op (M.op X2 X0) X1) X4 X3
       have i₂ := eq9731 X2 x X0 X1
       grind)
    | exact superpose eq9731 eq67
    | exact resolve eq67 eq9731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq9731
  have eq10465 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 (M.op X0 X1)) X5) = (M.op X1 (M.op X1 (M.op (M.op X4 (M.op (M.op X2 X0) X1)) (M.op (M.op (M.op X2 X0) X1) X5)))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq10397 X0 X1 X2 x X4 X5
       have i₂ := eq99 (M.op (M.op X4 (M.op (M.op X2 X0) X1)) (M.op (M.op (M.op X2 X0) X1) X5)) (M.op X2 X0) X1 x
       grind)
    | exact superpose eq99 eq10397
    | exact resolve eq10397 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10397
  have eq10472 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10378 X0
       have i₂ := eq77 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq77 eq10378
    | exact resolve eq10378 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq10378
  have eq10584 : ∀ X0 X1 X5 : G, (M.op (M.op X0 (M.op X0 X1)) X5) = (M.op X1 (M.op X1 (M.op X1 (M.op X1 X5)))) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq10465 X0 X1 x x X5
       have i₂ := eq94 X5 x (M.op x X0) X1
       grind)
    | exact superpose eq94 eq10465
    | exact resolve eq10465 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10465
  have eq10689 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1 (σ (M.op (M.op X0 X0) X0))
       have i₂ := eq10472 X0
       grind)
    | exact superpose eq10472 eq254
    | exact resolve eq254 eq10472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12709 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10689 X0 (σ X0)
       have i₂ := eq10472 X0
       grind)
    | exact superpose eq10472 eq10689
    | exact resolve eq10689 eq10472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10472 eq10689
  have eq13065 : ∀ X0 X1 : G, (M.op (M.op X0 (σ X1)) (σ X1)) = (σ (M.op (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12709 X1
       have i₂ := eq254 X1 (σ X1) X0
       grind)
    | exact superpose eq254 eq12709
    | exact resolve eq12709 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq12709
  have eq14172 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (τ (M.op (M.op X0 (σ X1)) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (M.op X1 X1) X1)
       have i₂ := eq13065 X0 X1
       grind)
    | exact superpose eq13065 eq10
    | exact resolve eq10 eq13065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13065
  have eq22924 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq830 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq830
    | (have j0 := eq830 (τ X0) X1
       grind)
    | exact resolve eq830 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq23225 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22924 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq22924
    | (have j0 := eq22924 X0 X1
       grind)
    | exact resolve eq22924 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22924
  have eq23296 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 (τ X0))) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23225 X0 X1
       have i₂ := eq149 X0
       grind)
    | exact superpose eq149 eq23225
    | (have j0 := eq23225 X0 X1
       grind)
    | exact resolve eq23225 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq23225
  have eq23335 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23296 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq23296
    | (have j0 := eq23296 X0 X1
       grind)
    | exact resolve eq23296 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23296
  have eq25754 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) X3)) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X0 X1 X2 X3 x
       have i₂ := eq99 X3 (M.op X2 X1) (M.op X1 X0) x
       grind)
    | exact superpose eq99 eq64
    | exact resolve eq64 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq99
  have eq56044 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op (M.op X1 X2) (M.op X2 X3))) X4) = (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 X3))) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq233 X0 X1 X2 X3 X4 X5
       have i₂ := eq231 (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 X3))) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X4)) X1 X2 X3
       grind)
    | exact superpose eq231 eq233
    | exact resolve eq233 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq233
  have eq56045 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op (M.op X1 X2) (M.op X2 X3))) X4) = (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 X3))) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56044 X0 X1 X2 X3 X4 X5
       have i₂ := eq25754 X3 X2 X1 (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 X3))) (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X4))
       grind)
    | exact superpose eq25754 eq56044
    | exact resolve eq56044 eq25754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25754 eq56044
  have eq56046 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op (M.op X1 X2) (M.op X2 X3))) X4) = (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4)))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56045 x X1 X2 X3 X4 X5
       have i₂ := eq94 X4 x (M.op X1 X2) (M.op X2 X3)
       grind)
    | exact superpose eq94 eq56045
    | exact resolve eq56045 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq56045
  have eq56047 : ∀ X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq56046 x X2 X3 X4 x
       have i₂ := eq248 X3 X2 x X4 x
       grind)
    | exact superpose eq248 eq56046
    | exact resolve eq56046 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq56046
  have eq56172 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (M.op (σ X0) (σ X1)) (M.op (M.op (σ X0) (σ X1)) (M.op (M.op (σ X0) (σ X1)) (M.op (M.op (σ X0) (σ X1)) X2)))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56047 (σ X1) (σ X0) x
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq56047 (σ X0) (σ X1) x
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq56047
    | (have j1 := eq181 X0 X1
       grind)
    | exact resolve eq56047 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56745 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) X2) = (M.op (σ X1) X2) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56172 X0 X1 X2
       have i₂ := eq56047 (σ X0) (σ X1) X2
       grind)
    | (have i₁ := eq56172 X0 X1 X2
       have i₂ := eq56047 X2 (M.op (σ X0) (σ X1)) (M.op (M.op (σ X0) (σ X1)) (M.op (M.op (σ X0) (σ X1)) (M.op (M.op (σ X0) (σ X1)) X2)))
       grind)
    | exact superpose eq56047 eq56172
    | (have j0 := eq56172 X0 X1 X2
       grind)
    | exact resolve eq56172 eq56047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56172
  have eq66957 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X2 (M.op X3 X0))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10584 X2 (M.op X3 X0) X1
       have i₂ := eq56047 X3 X0 X1
       grind)
    | exact superpose eq56047 eq10584
    | exact resolve eq10584 eq56047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10584 eq56047
  have eq69106 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq66957 X3 X4 X1 X2
       have i₂ := eq104 (M.op X1 (M.op X2 X3)) X4 X1 X0
       grind)
    | (have i₁ := eq66957 X3 X4 X1 X2
       have i₂ := eq104 (M.op X1 (M.op X2 X3)) X4 X0 X1
       grind)
    | exact superpose eq104 eq66957
    | exact resolve eq66957 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66957
  have eq99592 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq162 X0 (σ X0) X1
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq162
    | exact resolve eq162 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq100524 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq99592 X0 X1
       have i₂ := eq145 (M.op X0 X0)
       grind)
    | exact superpose eq145 eq99592
    | exact resolve eq99592 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq99592
  have eq881398 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23335 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23335
    | exact resolve eq23335 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23335
  have eq1595642 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq881398 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881398
  have eq1909112 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1595642 (σ X0) (σ X1)
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq1595642 (σ X1) (σ X0)
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq1595642
    | (have j0 := eq1595642 (σ X0) (σ X1)
       have j1 := eq181 X0 X1
       grind)
    | (have r₁ := eq1595642 (σ X0) (σ X0)
       have r₂ := eq181 X0 X0
       grind)
    | (have r₁ := eq1595642 (σ X1) (σ X1)
       have r₂ := eq181 X1 X1
       grind)
    | exact resolve eq1595642 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq1595642
  have eq1909538 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1909112 X0 X1
       have j1 := eq56745 X0 X1 x
       grind)
    | (have r₁ := eq1909112 X0 X1
       have r₂ := eq56745 X0 X1 (σ X1)
       grind)
    | (have r₁ := eq1909112 X1 X0
       have r₂ := eq56745 X0 X1 (σ X0)
       grind)
    | exact resolve eq1909112 eq56745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56745 eq1909112
  have eq1909897 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1909538 X0 X1
       have j1 := eq814 X1 X0
       grind)
    | (have r₁ := eq1909538 X1 X0
       have r₂ := eq814 X0 X1
       grind)
    | (have r₁ := eq1909538 X1 X1
       have r₂ := eq814 X1 X1
       grind)
    | exact resolve eq1909538 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq1909538
  have eq1910118 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1909897 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1909897
    | (have j0 := eq1909897 X0 X1
       grind)
    | exact resolve eq1909897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909897
  have eq1910215 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1910118 X0 X1
       have j1 := eq813 X1 X0
       grind)
    | (have r₁ := eq1910118 X1 X0
       have r₂ := eq813 X0 X1
       grind)
    | (have r₁ := eq1910118 X1 X1
       have r₂ := eq813 X1 X1
       grind)
    | exact resolve eq1910118 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq1910118
  have eq1910472 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1910215 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1910215
    | exact resolve eq1910215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1910739 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1910215 y x
       grind)
    | exact superpose eq1910215 eq16
    | (have j1 := eq1910215 y x
       grind)
    | exact resolve eq16 eq1910215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910215
  have eq1912417 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1910472 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1910472
    | (have j0 := eq1910472 X0 X1
       grind)
    | exact resolve eq1910472 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1910472
  have eq1913825 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1912417 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1912417
    | exact resolve eq1912417 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912417
  have eq1919994 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1910739
       have i₂ := eq1913825 y x
       grind)
    | exact superpose eq1913825 eq1910739
    | (have j1 := eq1913825 (σ y) (σ x)
       grind)
    | exact resolve eq1910739 eq1913825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910739 eq1913825
  have eq1920002 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1919994
  have eq1920124 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq1920002
       grind)
    | exact superpose eq1920002 eq9
    | exact resolve eq9 eq1920002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920002
  have eq1920830 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1920124 x
       have i₂ := eq100524 x x
       grind)
    | exact superpose eq100524 eq1920124
    | exact resolve eq1920124 eq100524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100524 eq1920124
  have eq1952802 : ∀ X0 : G, (τ (M.op (M.op X0 (σ y)) (σ y))) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) (M.op x x))) (M.op (M.op x x) (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14172 X0 (M.op (M.op x x) (M.op x x))
       have i₂ := eq1920830
       grind)
    | exact superpose eq1920830 eq14172
    | exact resolve eq14172 eq1920830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920830
  have eq1953062 : ∀ X0 : G, (τ (M.op (M.op X0 (σ y)) (σ y))) = (M.op x (M.op (M.op x x) (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1952802 X0
       have i₂ := eq69106 (M.op (M.op x x) (M.op x x)) (M.op x x) x x (M.op (M.op x x) (M.op x x))
       grind)
    | exact superpose eq69106 eq1952802
    | exact resolve eq1952802 eq69106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69106 eq1952802
  have eq1953320 : ∀ X0 : G, x = (τ (M.op (M.op X0 (σ y)) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1953062 X0
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq1953062
    | exact resolve eq1953062 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953062
  have eq1953486 : x = (M.op (M.op y y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1953320 x
       have i₂ := eq14172 x y
       grind)
    | exact superpose eq14172 eq1953320
    | exact resolve eq1953320 eq14172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14172 eq1953320
  have eq1953712 : ∀ X0 : G, x = (M.op (M.op X0 y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1953486
       have i₂ := eq104 y y y X0
       grind)
    | (have i₁ := eq1953486
       have i₂ := eq104 y y X0 y
       grind)
    | exact superpose eq104 eq1953486
    | exact resolve eq1953486 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1953486
  have eq1954575 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1953712 (M.op x y)
       have i₂ := eq1953712 x
       grind)
    | exact superpose eq1953712 eq1953712
    | exact resolve eq1953712 eq1953712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953712
  have eq1955559 : x = (M.op x y) := by grind
  clear eq1954575
  have eq1955896 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq1955559
       grind)
    | exact superpose eq1955559 eq9
    | exact resolve eq9 eq1955559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958036 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq987 x x
       have i₂ := eq1955896 x
       grind)
    | exact superpose eq1955896 eq987
    | exact resolve eq987 eq1955896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987 eq1955896
  have eq1959364 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1958036
       grind)
    | exact superpose eq1958036 eq16
    | exact resolve eq16 eq1958036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958036
  have eq1960262 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1959364
       have i₂ := eq1955559
       grind)
    | exact superpose eq1955559 eq1959364
    | exact resolve eq1959364 eq1955559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955559 eq1959364
  have eq1960263 : False := by grind
  exact eq1960263

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq510 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq476 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq511 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq510 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq517 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq511 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq511 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq511 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq526 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq517
    | (have j0 := eq517 X0 X1
       grind)
    | exact resolve eq517 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq527 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq526 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq532 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq527 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq527
    | exact resolve eq527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq527 x y
       grind)
    | exact superpose eq527 eq16
    | exact resolve eq16 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq639 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq532 X0 (τ X1)
       grind)
    | exact superpose eq532 eq17
    | exact resolve eq17 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq532
  have eq657 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq639
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq667 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq657
    | exact resolve eq657 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq691 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq543
       have i₂ := eq667 x y
       grind)
    | exact superpose eq667 eq543
    | exact resolve eq543 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq667
  have eq692 : False := by grind
  exact eq692

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq65 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq66 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq70 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22 eq36
  have eq85 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq85 y x
       grind)
    | exact superpose eq85 eq77
    | (have j1 := eq85 y x
       grind)
    | exact resolve eq77 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq116
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq85
    | (have j0 := eq85 (σ y) (σ x)
       grind)
    | exact resolve eq85 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq144 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq66
    | exact resolve eq66 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq145 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq27
    | exact resolve eq27 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq70
    | (have r₁ := eq70
       have r₂ := eq130
       grind)
    | exact resolve eq70 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq130
  have eq420 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq419
  have eq421 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq420
       have r₂ := eq144
       grind)
    | exact resolve eq420 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq420
  have eq424 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq421 eq117
    | exact resolve eq117 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq421
  have eq428 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq424
  have eq433 : y = (M.op x y) := by
    first
    | (have r₁ := eq428
       have r₂ := eq145
       grind)
    | exact resolve eq428 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq428
  have eq436 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq433 eq20
    | exact resolve eq20 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq440 : x ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq433 eq65
    | exact resolve eq65 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq441 : y ≠ y ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq433 eq69
    | (have r₁ := eq69
       have r₂ := eq433
       grind)
    | exact resolve eq69 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq433
  have eq446 : x = y ∨ y = (k y x) := by grind
  clear eq441
  have eq452 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq436
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq436
    | exact resolve eq436 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq454 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq452 eq26
    | exact resolve eq26 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq681 : y = (k y x) := by
    first
    | (have r₁ := eq446
       have r₂ := eq440
       grind)
    | exact resolve eq446 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq446
  have eq756 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq681
       grind)
    | exact superpose eq681 eq77
    | exact resolve eq77 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq681
  have eq763 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq452 eq756
    | exact resolve eq756 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq765 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq763
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq763
    | exact resolve eq763 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq763
  have eq766 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq452 eq765
    | exact resolve eq765 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq765
  have eq769 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq766 eq85
    | (have j0 := eq85 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq85 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq766
  have eq770 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq769
  have eq772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq454 eq770
    | exact resolve eq770 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq770
  have eq775 : False := by grind
  exact eq775
