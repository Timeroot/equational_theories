import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_pyy_pxy_pyy_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq10
    | exact resolve eq10 eq64
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
  clear eq43
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
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq66
    | exact resolve eq66 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq66
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq90 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x x) = (k y x) := by
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
  have eq91 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq98
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq798 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq71 X1
       grind)
    | exact superpose eq71 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq75
  have eq817 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq798 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq798
    | (have j0 := eq798 y X0
       grind)
    | exact resolve eq798 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq798
  have eq6004 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq817 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq817
    | (have j0 := eq817 x
       grind)
    | exact resolve eq817 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq817
  have eq6019 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6004
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq6004
    | exact resolve eq6004 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6004
  have eq6039 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq6019
    | exact resolve eq6019 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6019
  have eq6046 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq6039
    | exact resolve eq6039 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6039
  have eq6052 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6046
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq6046
    | exact resolve eq6046 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6046
  have eq6058 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq6052
    | exact resolve eq6052 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6052
  have eq14755 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq14755
    | exact resolve eq14755 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14755
  have eq14767 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq14756
       have r₂ := eq27
       grind)
    | exact resolve eq14756 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14756
  have eq14771 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq14767
    | exact resolve eq14767 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14767
  have eq14773 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq14771
    | exact resolve eq14771 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14771
  have eq14776 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq14773 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq14773
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14773
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14773
       grind)
    | exact resolve eq13 eq14773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14773
  have eq14787 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq14776
       have r₂ := eq26
       grind)
    | exact resolve eq14776 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14776
  have eq14795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq14787 eq116
    | exact resolve eq116 eq14787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14787
  have eq14803 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq14795
  have eq14805 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq14803
       have r₂ := eq27
       grind)
    | exact resolve eq14803 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14803
  have eq15050 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq14805 eq91
    | (have r₁ := eq91
       have r₂ := eq14805
       grind)
    | exact resolve eq91 eq14805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14805
  have eq15074 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq15050
  have eq15442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq15074 eq116
    | exact resolve eq116 eq15074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15074
  have eq15450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq15442
  have eq15452 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq15450
       have r₂ := eq27
       grind)
    | exact resolve eq15450 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15450
  have eq15455 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq15452 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15452
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15452
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15452
       grind)
    | exact resolve eq13 eq15452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15452
  have eq15466 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq15455
       have r₂ := eq26
       grind)
    | exact resolve eq15455 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15455
  have eq15475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq15466 eq116
    | exact resolve eq116 eq15466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq15466
  have eq15483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq15475
  have eq15485 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq15483
       have r₂ := eq27
       grind)
    | exact resolve eq15483 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15483
  have eq15488 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15485
       grind)
    | exact superpose eq15485 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq15485
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15485
       grind)
    | exact resolve eq13 eq15485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15485
  have eq15499 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq15488
       have r₂ := eq18
       grind)
    | exact resolve eq15488 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15488
  have eq15751 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq15499
       grind)
    | exact superpose eq15499 eq98
    | exact resolve eq98 eq15499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15499
  have eq15769 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq15751
    | exact resolve eq15751 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15751
  have eq15810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq15769 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq15769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15817 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq15810
    | exact resolve eq15810 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15810
  have eq15828 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq15817
       have r₂ := eq27
       grind)
    | exact resolve eq15817 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15817
  have eq15832 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq15828
    | exact resolve eq15828 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15828
  have eq15834 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq15832
    | exact resolve eq15832 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15832
  have eq17234 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq15834 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15834
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15834
       grind)
    | exact resolve eq13 eq15834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15834
  have eq17245 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq17234
       have r₂ := eq26
       grind)
    | exact resolve eq17234 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17234
  have eq17265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq17245 eq15769
    | exact resolve eq15769 eq17245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17245
  have eq17271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq17265
  have eq17279 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq17271
       have r₂ := eq27
       grind)
    | exact resolve eq17271 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17271
  have eq17282 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq17279 eq91
    | (have r₁ := eq91
       have r₂ := eq17279
       grind)
    | exact resolve eq91 eq17279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq17279
  have eq17307 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq17282
  have eq18065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq17307 eq15769
    | exact resolve eq15769 eq17307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17307
  have eq18071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq18065
  have eq18079 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq18071
       have r₂ := eq27
       grind)
    | exact resolve eq18071 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18071
  have eq18082 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18079 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18079
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18079
       grind)
    | exact resolve eq13 eq18079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18079
  have eq18093 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq18082
       have r₂ := eq26
       grind)
    | exact resolve eq18082 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18082
  have eq18113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18093 eq15769
    | exact resolve eq15769 eq18093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15769 eq18093
  have eq18119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq18113
  have eq18127 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq18119
       have r₂ := eq27
       grind)
    | exact resolve eq18119 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18119
  have eq18131 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq18127
       grind)
    | exact superpose eq18127 eq70
    | exact resolve eq70 eq18127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq18132 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18127
       grind)
    | exact superpose eq18127 eq90
    | (have r₁ := eq90
       have r₂ := eq18127
       grind)
    | exact resolve eq90 eq18127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq18127
  have eq18158 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq18132
  have eq18171 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq18131
    | exact resolve eq18131 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18131
  have eq18825 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18158
       grind)
    | exact superpose eq18158 eq98
    | exact resolve eq98 eq18158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18158
  have eq18847 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq18825
    | exact resolve eq18825 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18825
  have eq19150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq18847 eq6058
    | exact resolve eq6058 eq18847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19167 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19150
       have r₂ := eq27
       grind)
    | exact resolve eq19150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19150
  have eq19180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq18171 eq19167
    | exact resolve eq19167 eq18171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19167
  have eq19186 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19180
       have r₂ := eq27
       grind)
    | exact resolve eq19180 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19180
  have eq19196 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19186 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19186
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19186
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19186
       grind)
    | exact resolve eq13 eq19186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19186
  have eq19207 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19196
       have r₂ := eq26
       grind)
    | exact resolve eq19196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19196
  have eq19515 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19207 eq18847
    | exact resolve eq18847 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18847 eq19207
  have eq19517 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq19515
  have eq19521 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19517
       have r₂ := eq27
       grind)
    | exact resolve eq19517 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19517
  have eq19807 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19521
       grind)
    | exact superpose eq19521 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq19521
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19521
       grind)
    | exact resolve eq13 eq19521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19521
  have eq19818 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq19807
       have r₂ := eq18
       grind)
    | exact resolve eq19807 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19807
  have eq19822 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19818
       grind)
    | exact superpose eq19818 eq98
    | exact resolve eq98 eq19818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq19818
  have eq19844 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq19822
    | exact resolve eq19822 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19822
  have eq20186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19844 eq6058
    | exact resolve eq6058 eq19844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6058
  have eq20198 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq20186
       have r₂ := eq27
       grind)
    | exact resolve eq20186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20186
  have eq20211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq18171 eq20198
    | exact resolve eq20198 eq18171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18171 eq20198
  have eq20217 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq20211
       have r₂ := eq27
       grind)
    | exact resolve eq20211 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20211
  have eq20612 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20217 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20217
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20217
       grind)
    | exact resolve eq13 eq20217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20217
  have eq20623 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq20612
       have r₂ := eq26
       grind)
    | exact resolve eq20612 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq20612
  have eq20625 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19844 eq20623
    | exact resolve eq20623 eq19844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19844 eq20623
  have eq20627 : False := by grind
  exact eq20627

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_x_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq68
  have eq412 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2859 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq412 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq412
    | exact resolve eq412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq2900 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2859 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2859
    | (have j0 := eq2859 X0 X1
       grind)
    | exact resolve eq2859 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq2904 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ X1) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2900 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq2900
    | (have j0 := eq2900 (τ X0) (τ X1)
       grind)
    | exact resolve eq2900 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2900
  have eq2994 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2904 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2904
    | (have j0 := eq2904 X0 X1
       grind)
    | exact resolve eq2904 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq17456 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq2994 X0 X1
       grind)
    | (have i₁ := eq12 (τ X0) (τ X1)
       have i₂ := eq2994 X0 X1
       grind)
    | exact superpose eq2994 eq12
    | (have j1 := eq2994 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) (τ X1)
       have r₂ := eq2994 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) (τ X0)
       have r₂ := eq2994 X0 X1
       grind)
    | exact resolve eq12 eq2994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2994
  have eq17463 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq17456 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17456
  have eq17477 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17463 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq17463
    | (have j0 := eq17463 X0 X1
       grind)
    | exact resolve eq17463 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq17463
  have eq17517 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17477 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17477
    | exact resolve eq17477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17477
  have eq17588 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17517 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq17517
    | (have j0 := eq17517 X0 X1
       grind)
    | exact resolve eq17517 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17517
  have eq17639 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) X0)
       have i₂ := eq17588 X0 X1
       grind)
    | exact superpose eq17588 eq10
    | (have j1 := eq17588 X0 X1
       grind)
    | exact resolve eq10 eq17588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17588
  have eq17749 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17639 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq17639
    | (have j0 := eq17639 X0 X1
       grind)
    | exact resolve eq17639 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17639
  have eq17750 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17749 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17749
  have eq17771 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17750 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17750
    | exact resolve eq17750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17810 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq17750 X1 X0
       grind)
    | exact superpose eq17750 eq19
    | (have j1 := eq17750 X1 X0
       grind)
    | exact resolve eq19 eq17750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17750
  have eq18112 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq17771 (σ X0) (σ X1)
       grind)
    | exact superpose eq17771 eq15
    | (have j1 := eq17771 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17771
  have eq18240 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17810 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17810
    | exact resolve eq17810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17810
  have eq18396 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18240 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18240
    | (have j0 := eq18240 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq18240 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18240
  have eq19793 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18112 x y
       grind)
    | exact superpose eq18112 eq16
    | (have j1 := eq18112 x y
       grind)
    | exact resolve eq16 eq18112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18112
  have eq19841 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19793
       have i₂ := eq18396 x y
       grind)
    | exact superpose eq18396 eq19793
    | (have j1 := eq18396 (σ x) (σ y)
       grind)
    | (have r₁ := eq19793
       have r₂ := eq18396 x y
       grind)
    | (have r₁ := eq19793
       have r₂ := eq18396 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq19793
       have r₂ := eq18396 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq19793 eq18396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18396 eq19793
  have eq19844 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq19841
  have eq19847 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19844
       grind)
    | exact superpose eq19844 eq16
    | exact resolve eq16 eq19844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19844
  have eq19848 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq19847
       have r₂ := eq79 x
       grind)
    | exact resolve eq19847 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19847
  have eq19849 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19848
       grind)
    | exact superpose eq19848 eq16
    | exact resolve eq16 eq19848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19850 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19848
       grind)
    | exact superpose eq19848 eq10
    | exact resolve eq10 eq19848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19848
  have eq20021 : x = y := by
    first
    | (have i₁ := eq19850
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19850
    | exact resolve eq19850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19850
  have eq20022 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq19849
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq19849
    | exact resolve eq19849 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq19849
  have eq20023 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20022
       have i₂ := eq20021
       grind)
    | exact superpose eq20021 eq20022
    | exact resolve eq20022 eq20021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20021 eq20022
  have eq20024 : False := by grind
  exact eq20024

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq73 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq627 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq11550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11550
    | exact resolve eq11550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11550
  have eq11562 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11551
       have r₂ := eq28
       grind)
    | exact resolve eq11551 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11551
  have eq11564 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11562
    | exact resolve eq11562 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11562
  have eq11566 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11564
  have eq11576 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11566
    | exact resolve eq11566 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11566
  have eq11582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11576 eq111
    | exact resolve eq111 eq11576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11576
  have eq11594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11582
  have eq11596 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11594
       have r₂ := eq28
       grind)
    | exact resolve eq11594 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11594
  have eq11712 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11596
  have eq11722 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11712
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11712
    | exact resolve eq11712 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11712
  have eq11725 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11722
       grind)
    | exact superpose eq11722 eq69
    | exact resolve eq69 eq11722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11722
  have eq11747 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11725
    | exact resolve eq11725 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11725
  have eq11911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11747 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11911
    | exact resolve eq11911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11911
  have eq11925 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11914
       have r₂ := eq28
       grind)
    | exact resolve eq11914 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11914
  have eq11927 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11925
    | exact resolve eq11925 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11925
  have eq11928 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11927
  have eq11931 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11928
  have eq11941 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11931
    | exact resolve eq11931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11931
  have eq12068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11941 eq11747
    | exact resolve eq11747 eq11941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11747 eq11941
  have eq12074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12068
  have eq12078 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12074
       have r₂ := eq28
       grind)
    | exact resolve eq12074 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12074
  have eq12080 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12078 eq28
    | exact resolve eq28 eq12078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12082 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12078 eq73
    | (have r₁ := eq73
       have r₂ := eq12078
       grind)
    | exact resolve eq73 eq12078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq12078
  have eq12087 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12082
  have eq12343 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12087 eq111
    | exact resolve eq111 eq12087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12363 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq12343
  have eq12377 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12363
       have r₂ := eq12080
       grind)
    | exact resolve eq12363 eq12080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12363
  have eq12383 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq12377
  have eq12393 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12383
    | exact resolve eq12383 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12383
  have eq12527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12393 eq111
    | exact resolve eq111 eq12393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq12393
  have eq12543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq12527
  have eq12547 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12543
       have r₂ := eq28
       grind)
    | exact resolve eq12543 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12543
  have eq12615 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq12547
  have eq12625 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12615
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12615
    | exact resolve eq12615 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12615
  have eq12628 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq12625
       grind)
    | exact superpose eq12625 eq69
    | exact resolve eq69 eq12625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12625
  have eq12650 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq12628
    | exact resolve eq12628 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12628
  have eq12687 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12650 eq12087
    | exact resolve eq12087 eq12650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12087
  have eq12695 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12687
  have eq12703 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12695
       have r₂ := eq12080
       grind)
    | exact resolve eq12695 eq12080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12080 eq12695
  have eq12719 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12703
  have eq12729 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12719
    | exact resolve eq12719 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12719
  have eq12748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12729 eq12650
    | exact resolve eq12650 eq12729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12650 eq12729
  have eq12754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12748
  have eq12762 : y = (M.op x y) := by
    first
    | (have r₁ := eq12754
       have r₂ := eq28
       grind)
    | exact resolve eq12754 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12754
  have eq12764 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq12762 eq21
    | exact resolve eq21 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq12770 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq12762 eq72
    | (have r₁ := eq72
       have r₂ := eq12762
       grind)
    | exact resolve eq72 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq12822 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq12770
  have eq12873 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12764
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12764
    | exact resolve eq12764 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12764
  have eq12875 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12873 eq27
    | exact resolve eq27 eq12873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq13096 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq12822
       grind)
    | exact superpose eq12822 eq69
    | exact resolve eq69 eq12822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13108 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq627 x y
       have i₂ := eq12822
       grind)
    | exact superpose eq12822 eq627
    | (have j0 := eq627 x y
       grind)
    | exact resolve eq627 eq12822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12822
  have eq13111 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq13108
  have eq13118 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13111
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13111
    | exact resolve eq13111 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13111
  have eq13128 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12873 eq13096
    | exact resolve eq13096 eq12873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13096
  have eq13130 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12873 eq13118
    | exact resolve eq13118 eq12873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13118
  have eq13140 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13128
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13128
    | exact resolve eq13128 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13128
  have eq13141 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13130
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13130
    | exact resolve eq13130 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13130
  have eq13150 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12873 eq13140
    | exact resolve eq13140 eq12873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13140
  have eq13151 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12875 eq13141
    | exact resolve eq13141 eq12875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13141
  have eq13155 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13151
       have r₂ := eq28
       grind)
    | exact resolve eq13151 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13151
  have eq13159 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13155
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13155
    | exact resolve eq13155 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13155
  have eq13163 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13159
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13159
    | exact resolve eq13159 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13159
  have eq13167 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12873 eq13163
    | exact resolve eq13163 eq12873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13163
  have eq13244 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq13167
  have eq13258 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12875 eq13244
    | exact resolve eq13244 eq12875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13244
  have eq13273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13258 eq13150
    | exact resolve eq13150 eq13258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13150 eq13258
  have eq13279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq13273
  have eq13281 : y = (M.op x x) := by
    first
    | (have r₁ := eq13279
       have r₂ := eq28
       grind)
    | exact resolve eq13279 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13279
  have eq13295 : (M.op x y) = (k y x) := by grind
  clear eq13281
  have eq13305 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13295
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13295
    | exact resolve eq13295 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq13295
  have eq13307 : y = (k y x) := by
    first
    | exact superpose eq12762 eq13305
    | exact resolve eq13305 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12762 eq13305
  have eq13316 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq13307
       grind)
    | exact superpose eq13307 eq69
    | exact resolve eq69 eq13307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq13328 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq627 x y
       have i₂ := eq13307
       grind)
    | exact superpose eq13307 eq627
    | (have j0 := eq627 x y
       grind)
    | exact resolve eq627 eq13307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq13307
  have eq13331 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq13328
  have eq13337 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13331
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13331
    | exact resolve eq13331 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13331
  have eq13347 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq12873 eq13316
    | exact resolve eq13316 eq12873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13316
  have eq13348 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12873 eq13337
    | exact resolve eq13337 eq12873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13337
  have eq13358 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq13347
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13347
    | exact resolve eq13347 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13347
  have eq13359 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13348
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13348
    | exact resolve eq13348 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13348
  have eq13368 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq12873 eq13358
    | exact resolve eq13358 eq12873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13358
  have eq13369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12875 eq13359
    | exact resolve eq13359 eq12875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13359
  have eq13373 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq13369
       have r₂ := eq28
       grind)
    | exact resolve eq13369 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13369
  have eq13377 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13373
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13373
    | exact resolve eq13373 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13373
  have eq13381 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13377
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13377
    | exact resolve eq13377 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq13377
  have eq13385 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12873 eq13381
    | exact resolve eq13381 eq12873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12873 eq13381
  have eq13464 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq13385
  have eq13474 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq12875 eq13464
    | exact resolve eq13464 eq12875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12875 eq13464
  have eq13475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13368 eq13474
    | exact resolve eq13474 eq13368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13368 eq13474
  have eq13476 : False := by grind
  exact eq13476

/-- `Equation3479`: `x ◇ x = y ◇ ((x ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pxy_pxy_x_pyx_Equation3479 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3479 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3479.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 x) x)
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X0 x) x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 x X0 x
       have i₂ := eq65 x X1 x
       grind)
    | (have i₁ := eq65 X0 X1 (M.op X0 X0)
       have i₂ := eq65 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2141 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2130 X0 X1
       grind)
    | (have r₁ := eq2130 X0 X1
       have r₂ := eq76 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2130 X0 X1
       have r₂ := eq76 (σ X1) (σ X0)
       grind)
    | exact resolve eq2130 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq2162 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2141 x y
       grind)
    | exact superpose eq2141 eq16
    | exact resolve eq16 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141
  have eq3212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) ≠ (M.op y y) := by
    first
    | (have i₁ := eq2162
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq2162
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq2162 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq3213 : (M.op x x) ≠ (M.op y y) := by grind
  clear eq3212
  have eq3214 : False := by grind
  exact eq3214

/-- `Equation3479`: `x ◇ x = y ◇ ((x ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = X then Y else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_x_pxy_y_x_Equation3479 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) Law3479 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3479.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 x) x)
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X0 x) x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 x X0 x
       have i₂ := eq65 x X1 x
       grind)
    | (have i₁ := eq65 X0 X1 (M.op X0 X0)
       have i₂ := eq65 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2141 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2130 X0 X1
       grind)
    | (have r₁ := eq2130 X0 X1
       have r₂ := eq76 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2130 X0 X1
       have r₂ := eq76 (σ X1) (σ X0)
       grind)
    | exact resolve eq2130 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq2162 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2141 x y
       grind)
    | exact superpose eq2141 eq16
    | exact resolve eq16 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141
  have eq3212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) ≠ (M.op y y) := by
    first
    | (have i₁ := eq2162
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq2162
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq2162 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq3213 : (M.op x x) ≠ (M.op y y) := by grind
  clear eq3212
  have eq3214 : False := by grind
  exact eq3214

/-- `Equation3479`: `x ◇ x = y ◇ ((x ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_y_pxy_pyx_pyy_Equation3479 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) Law3479 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3479.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 x) x)
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X0 x) x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 x X0 x
       have i₂ := eq65 x X1 x
       grind)
    | (have i₁ := eq65 X0 X1 (M.op X0 X0)
       have i₂ := eq65 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2141 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2130 X0 X1
       grind)
    | (have r₁ := eq2130 X0 X1
       have r₂ := eq76 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2130 X0 X1
       have r₂ := eq76 (σ X1) (σ X0)
       grind)
    | exact resolve eq2130 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq2162 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2141 x y
       grind)
    | exact superpose eq2141 eq16
    | exact resolve eq16 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141
  have eq3212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) ≠ (M.op y y) := by
    first
    | (have i₁ := eq2162
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq2162
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq2162 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq3213 : (M.op x x) ≠ (M.op y y) := by grind
  clear eq3212
  have eq3214 : False := by grind
  exact eq3214

/-- `Equation3479`: `x ◇ x = y ◇ ((x ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then m(Y,X) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_y_pxy_pyx_y_Equation3479 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) Law3479 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3479.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 x) x)
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X0 x) x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 x X0 x
       have i₂ := eq65 x X1 x
       grind)
    | (have i₁ := eq65 X0 X1 (M.op X0 X0)
       have i₂ := eq65 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2141 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2130 X0 X1
       grind)
    | (have r₁ := eq2130 X0 X1
       have r₂ := eq76 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2130 X0 X1
       have r₂ := eq76 (σ X1) (σ X0)
       grind)
    | exact resolve eq2130 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq2162 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2141 x y
       grind)
    | exact superpose eq2141 eq16
    | exact resolve eq16 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141
  have eq3212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) ≠ (M.op y y) := by
    first
    | (have i₁ := eq2162
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq2162
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq2162 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq3213 : (M.op x x) ≠ (M.op y y) := by grind
  clear eq3212
  have eq3214 : False := by grind
  exact eq3214

/-- `Equation3479`: `x ◇ x = y ◇ ((x ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxx_pxy_pyx_Equation3479 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3479 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3479.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
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
  clear eq22
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
  clear eq24 eq35
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op (M.op (M.op X0 X1) X1) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X2 X3
       have i₂ := eq14 X0 (M.op (M.op X0 X1) X1) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 x) x)
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X0 x) x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) ≠ (M.op X3 X3) ∨ (M.op X3 X1) = X3 ∨ (k X1 X3) = (M.op X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X1 X3
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X3
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X2) X2)
       have r₂ := eq14 X0 (M.op (M.op X0 X2) X2) X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X2) X2) X0
       have r₂ := eq14 X0 (M.op (M.op X0 X2) X2) X2
       grind)
    | exact resolve eq12 eq14
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
    | (have r₁ := eq116 X0
       have r₂ := eq13 X0 X0
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
  have eq122 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq49
    | exact resolve eq49 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq123 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq122
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq122
    | exact resolve eq122 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq125 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq120
    | exact resolve eq120 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq146 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq143
       have i₂ := eq117 sF1
       grind)
    | exact superpose eq117 eq143
    | exact resolve eq143 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq149 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq146
       have i₂ := eq117 sF0
       grind)
    | exact superpose eq117 eq146
    | exact resolve eq146 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq146
  have eq171 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq149 eq16
    | exact resolve eq16 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0 x
       have i₂ := eq56 x X1 x
       grind)
    | (have i₁ := eq56 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X3 X2) = X3 ∨ (k X2 X3) = (M.op X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq56 X1 X2 X0
       grind)
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq56 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | (have r₁ := eq12 X1 (M.op X0 X0)
       have r₂ := eq56 X0 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq56 X0 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X2 X3 : G, (k X2 X3) = (M.op X2 X3) ∨ (M.op X3 X2) = X3 := by
    intro X2 X3
    first
    | (have j0 := eq292 x x X2 X3
       grind)
    | (have r₁ := eq292 X2 x X2 x
       have r₂ := eq56 x x X2
       grind)
    | (have r₁ := eq292 (M.op x x) x X2 (M.op x x)
       have r₂ := eq56 x (M.op x x) (M.op x x)
       grind)
    | exact resolve eq292 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq337 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq149
       have i₂ := eq288 sF0 x
       grind)
    | (have i₁ := eq149
       have i₂ := eq288 X0 sF0
       grind)
    | exact superpose eq288 eq149
    | exact resolve eq149 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq171
       have i₂ := eq288 sF1 x
       grind)
    | (have i₁ := eq171
       have i₂ := eq288 X0 sF1
       grind)
    | exact superpose eq288 eq171
    | exact resolve eq171 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq420 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (τ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq338 x
       have i₂ := eq56 X1 x X0
       grind)
    | (have i₁ := eq338 (M.op X0 X0)
       have i₂ := eq56 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq56 eq338
    | exact resolve eq338 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X2 X3) X3)) = (M.op X0 (M.op (M.op (M.op (M.op (M.op (M.op X1 (M.op (M.op X2 X3) X3)) X2) X4) X4) X5) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq54 X1 X2 X3 (M.op (M.op X1 (M.op (M.op X2 X3) X3)) X2)
       have i₂ := eq51 (M.op (M.op X1 (M.op (M.op X2 X3) X3)) X2) X4 X0 X5
       grind)
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq54
  have eq1077 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) X0) ∨ (k X0 (M.op (M.op X0 X1) X1)) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X0 x (M.op (M.op X0 X1) X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1078 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X1) X1)) ∨ (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq1077
    | (have j0 := eq1077 X0 X1
       grind)
    | exact resolve eq1077 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1101 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1078 X0 X1
       have j1 := eq13 X0 (M.op (M.op X0 X1) X1)
       grind)
    | (have r₁ := eq1078 X0 X1
       have r₂ := eq13 X0 (M.op (M.op X0 X1) X1)
       grind)
    | exact resolve eq1078 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1597 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1101 X1 (M.op x x)
       have i₂ := eq56 x X0 (M.op X1 (M.op x x))
       grind)
    | exact superpose eq56 eq1101
    | exact resolve eq1101 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1627 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1597 X2 X1
       have i₂ := eq288 X1 X0
       grind)
    | (have i₁ := eq1597 X2 X1
       have i₂ := eq288 X0 X1
       grind)
    | exact superpose eq288 eq1597
    | exact resolve eq1597 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1978 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq306 x y
       grind)
    | exact superpose eq306 eq44
    | (have j1 := eq306 x y
       grind)
    | exact resolve eq44 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2000 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1978
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1978
    | exact resolve eq1978 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1978
  have eq2003 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq2000
    | exact resolve eq2000 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq2007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2003 eq306
    | (have j0 := eq306 (σ x) (σ y)
       grind)
    | exact resolve eq306 eq2003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2009 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq2007
    | exact resolve eq2007 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2012 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq2009
       have r₂ := eq27
       grind)
    | exact resolve eq2009 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009
  have eq2014 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2012 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2012
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2012
       grind)
    | exact resolve eq13 eq2012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2015 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) (σ x))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2012 eq14
    | exact resolve eq14 eq2012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2025 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq2014
  have eq2032 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2025 eq2003
    | exact resolve eq2003 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003
  have eq2033 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2025 eq62
    | exact resolve eq62 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2025
  have eq2036 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq2032
  have eq2038 : (k x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq123 eq2033
    | exact resolve eq2033 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033
  have eq2039 : (k x y) = (M.op x x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq2038
       have r₂ := eq13 x y
       grind)
    | exact resolve eq2038 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq2042 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2039
       grind)
    | exact superpose eq2039 eq44
    | exact resolve eq44 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2039
  have eq2046 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2042
       have i₂ := eq125
       grind)
    | exact superpose eq125 eq2042
    | exact resolve eq2042 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq2042
  have eq2053 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2046 eq306
    | (have j0 := eq306 (σ x) (σ y)
       grind)
    | exact resolve eq306 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq2046
  have eq2055 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq2053
    | exact resolve eq2053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053
  have eq2070 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2036 eq337
    | exact resolve eq337 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2071 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2036 eq338
    | exact resolve eq338 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq2091 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq2071
    | exact resolve eq2071 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2071
  have eq2158 : ∀ X0 : G, (M.op x y) = (τ (M.op X0 (M.op x y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2091 eq420
    | exact resolve eq420 eq2091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq2199 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2055 eq123
    | exact resolve eq123 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq2202 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq2055 eq56
    | exact resolve eq56 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2213 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq2055 eq1597
    | exact resolve eq1597 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597
  have eq2214 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq2055 eq1627
    | exact resolve eq1627 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq2216 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq2055 eq14
    | exact resolve eq14 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2260 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (M.op x y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2070
       have i₂ := eq288 sF1 x
       grind)
    | (have i₁ := eq2070
       have i₂ := eq288 X0 sF1
       grind)
    | exact superpose eq288 eq2070
    | exact resolve eq2070 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq2341 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op x y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2158 eq15
    | exact resolve eq15 eq2158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2158
  have eq2358 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op x y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20 eq2341
    | (have j0 := eq2341 X0
       grind)
    | exact resolve eq2341 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341
  have eq2437 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2358 eq2091
    | exact resolve eq2091 eq2358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091 eq2358
  have eq2439 : y = (M.op y x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq2437
  have eq2451 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq2439
       grind)
    | exact superpose eq2439 eq14
    | exact resolve eq14 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2645 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2199
       have i₂ := eq288 x X0
       grind)
    | (have i₁ := eq2199
       have i₂ := eq288 X0 x
       grind)
    | exact superpose eq288 eq2199
    | exact resolve eq2199 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq3053 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2055
       have i₂ := eq2645 sF2
       grind)
    | exact superpose eq2645 eq2055
    | exact resolve eq2055 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055 eq2645
  have eq3057 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq3053
  have eq3072 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq3057 eq14
    | exact resolve eq14 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9718 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (k X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2202 X0 X1
       have i₂ := eq2213 X0
       grind)
    | exact superpose eq2213 eq2202
    | exact resolve eq2202 eq2213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202 eq2213
  have eq9774 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (k X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have j0 := eq9718 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9718
  have eq11226 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq2216 eq2214
    | exact resolve eq2214 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214 eq2216
  have eq11265 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq11226 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11226
  have eq11300 : ∀ X0 : G, (σ (M.op (σ x) (σ y))) = (k X0 (σ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq11265 eq34
    | exact resolve eq34 eq11265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq11265
  have eq34914 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2451 X0
       have i₂ := eq2439
       grind)
    | exact superpose eq2439 eq2451
    | exact resolve eq2451 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439 eq2451
  have eq35087 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq34914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34914
  have eq35101 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq35087 X1
       have i₂ := eq288 y X0
       grind)
    | (have i₁ := eq35087 X1
       have i₂ := eq288 X0 y
       grind)
    | exact superpose eq288 eq35087
    | exact resolve eq35087 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35087
  have eq35481 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq35101 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35101
    | (have j0 := eq35101 X0 x
       grind)
    | exact resolve eq35101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35101
  have eq37980 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq149
       have i₂ := eq35481 sF0
       grind)
    | exact superpose eq35481 eq149
    | exact resolve eq149 eq35481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq38034 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq37980
    | exact resolve eq37980 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37980
  have eq38384 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq38034 eq35481
    | exact resolve eq35481 eq38034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35481 eq38034
  have eq38415 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq38384
  have eq44332 : ∀ X0 : G, (σ (M.op (σ x) (σ y))) = (σ (k X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq11300 (σ X0)
       have i₂ := eq10 X0 sF4
       grind)
    | exact superpose eq10 eq11300
    | exact resolve eq11300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11300
  have eq45377 : ∀ X0 X1 X2 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq337 (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) x) x) x) x)
       have i₂ := eq812 (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) x) x) x) x) X0 X1 X2 x x
       grind)
    | exact superpose eq812 eq337
    | exact resolve eq337 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq812
  have eq45573 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op x y)) = (σ (M.op X0 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq38415 eq45377
    | exact resolve eq45377 eq38415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45377
  have eq46545 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (τ (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op (M.op X1 X2) X2))
       have i₂ := eq45573 X0 X1 X2
       grind)
    | exact superpose eq45573 eq16
    | exact resolve eq16 eq45573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45573
  have eq46569 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46545 X0 X1 X2
       have i₂ := eq338 sF0
       grind)
    | exact superpose eq338 eq46545
    | exact resolve eq46545 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46545
  have eq64651 : ∀ X0 : G, (σ (M.op (σ x) (σ y))) = (σ (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq9774 eq44332
    | exact resolve eq44332 eq9774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9774 eq44332
  have eq64692 : ∀ X0 : G, (σ (M.op (σ x) (σ y))) = (σ (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq64651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64651
  have eq291225 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq3057 eq3072
    | exact resolve eq3072 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057 eq3072
  have eq291724 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq291225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291225
  have eq291920 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq291724 X0
       have i₂ := eq288 sF3 X1
       grind)
    | (have i₁ := eq291724 X0
       have i₂ := eq288 X0 sF3
       grind)
    | exact superpose eq288 eq291724
    | exact resolve eq291724 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291724
  have eq292995 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq291920
    | (have j0 := eq291920 X0 (σ x)
       grind)
    | exact resolve eq291920 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291920
  have eq294962 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq338 x
       have i₂ := eq292995 x
       grind)
    | exact superpose eq292995 eq338
    | exact resolve eq338 eq292995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq297106 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq294962 eq292995
    | exact resolve eq292995 eq294962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292995 eq294962
  have eq297180 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq297106
  have eq297304 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq297180 eq15
    | exact resolve eq15 eq297180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297180
  have eq475633 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2012 eq2015
    | exact resolve eq2015 eq2012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012 eq2015
  have eq476192 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq475633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475633
  have eq476379 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq476192 eq476192
    | exact resolve eq476192 eq476192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476192
  have eq476964 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq476379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476379
  have eq481128 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq476964
    | (have j0 := eq476964 X0 (σ x)
       grind)
    | exact resolve eq476964 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476964
  have eq482570 : (M.op (σ x) (σ y)) = (σ (σ (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq481128 eq2260
    | exact resolve eq2260 eq481128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260 eq481128
  have eq483025 : (M.op (σ x) (σ y)) = (σ (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq482570
  have eq483228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq38415 eq483025
    | exact resolve eq483025 eq38415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483025
  have eq483311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq483228
    | exact resolve eq483228 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483228
  have eq483327 : y = (M.op y x) := by
    first
    | (have r₁ := eq483311
       have r₂ := eq27
       grind)
    | exact resolve eq483311 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483311
  have eq483378 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq46569 X0 y x
       have i₂ := eq483327
       grind)
    | exact superpose eq483327 eq46569
    | exact resolve eq46569 eq483327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483453 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq483378 X0
       have i₂ := eq483327
       grind)
    | exact superpose eq483327 eq483378
    | exact resolve eq483378 eq483327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483327 eq483378
  have eq484109 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) := by
    intro X0 X1
    first
    | exact superpose eq483453 eq483453
    | exact resolve eq483453 eq483453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483453
  have eq486443 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq484109 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq484109
    | (have j0 := eq484109 X0 x
       grind)
    | exact resolve eq484109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq484109
  have eq487764 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq486443 y
       have i₂ := eq288 y X0
       grind)
    | (have i₁ := eq486443 y
       have i₂ := eq288 X0 y
       grind)
    | exact superpose eq288 eq486443
    | exact resolve eq486443 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq486443
  have eq490152 : (σ (M.op x y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq64692 sF4
       have i₂ := eq487764 sF4
       grind)
    | exact superpose eq487764 eq64692
    | exact resolve eq64692 eq487764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64692
  have eq490542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq297304 eq490152
    | exact resolve eq490152 eq297304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297304 eq490152
  have eq491040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq490542
    | exact resolve eq490542 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq490542
  have eq491142 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq491040
       have r₂ := eq27
       grind)
    | exact resolve eq491040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491040
  have eq495329 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq491142 eq46569
    | exact resolve eq46569 eq491142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46569
  have eq495403 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq491142 eq495329
    | exact resolve eq495329 eq491142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491142 eq495329
  have eq495467 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq495403 X0
       have i₂ := eq487764 sF0
       grind)
    | exact superpose eq487764 eq495403
    | exact resolve eq495403 eq487764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487764 eq495403
  have eq495577 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq495467
    | (have j0 := eq495467 (σ x)
       grind)
    | exact resolve eq495467 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq495467
  have eq496892 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq495577 eq27
    | exact resolve eq27 eq495577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq495577
  have eq497322 : False := by grind
  exact eq497322
