import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq78 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq96
    | (have j0 := eq96 (σ X0) (σ X1)
       grind)
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq44
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq44 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ x) (σ y)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq159 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq712 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq79
    | (have r₁ := eq79
       have r₂ := eq131
       grind)
    | exact resolve eq79 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq131
  have eq713 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq712
  have eq727 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq713 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq713
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq713
       grind)
    | exact resolve eq13 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq735 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq727
  have eq747 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq735
    | exact resolve eq735 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq755 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq747
    | exact resolve eq747 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq747
  have eq763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq755
  have eq766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq763
       have r₂ := eq133
       grind)
    | exact resolve eq763 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq763
  have eq767 : x = (M.op x y) := by
    first
    | (have r₁ := eq766
       have r₂ := eq27
       grind)
    | exact resolve eq766 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq768 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq767 eq20
    | exact resolve eq20 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : x ≠ x ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq767 eq78
    | (have r₁ := eq78
       have r₂ := eq767
       grind)
    | exact resolve eq78 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq779 : y = (M.op y x) ∨ x = (k x y) := by grind
  clear eq774
  have eq786 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq768
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq768
    | exact resolve eq768 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq899 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq786 eq26
    | exact resolve eq26 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq979 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq100
    | (have j0 := eq100 (M.op x y) X0
       grind)
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq100
  have eq1019 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq767 eq979
    | (have j0 := eq979 X0
       grind)
    | exact resolve eq979 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1567 : (σ (k x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1019 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1019
    | (have j0 := eq1019 y
       grind)
    | exact resolve eq1019 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1019
  have eq1585 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq899 eq1567
    | exact resolve eq1567 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq1599 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1585
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1585
    | exact resolve eq1585 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1585
  have eq1610 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq786 eq1599
    | exact resolve eq1599 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq1616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq899 eq1610
    | exact resolve eq1610 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1610
  have eq1618 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq1616
       have r₂ := eq27
       grind)
    | exact resolve eq1616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1620 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq1618 eq159
    | exact resolve eq159 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq1618
  have eq1622 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq767 eq1620
    | exact resolve eq1620 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620
  have eq1713 : y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq779
       have i₂ := eq1622
       grind)
    | exact superpose eq1622 eq779
    | exact resolve eq779 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq1726 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1713
       grind)
    | exact superpose eq1713 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1713
       grind)
    | exact resolve eq13 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1739 : (M.op x y) = (k x y) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1726
  have eq1741 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1739
       have i₂ := eq1622
       grind)
    | exact superpose eq1622 eq1739
    | exact resolve eq1739 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622 eq1739
  have eq1752 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1741
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1741
    | exact resolve eq1741 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1741
  have eq1760 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq767 eq1752
    | exact resolve eq1752 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq1752
  have eq1761 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1760
  have eq1765 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1761 eq15
    | exact resolve eq15 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761
  have eq1766 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1765
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1765
    | exact resolve eq1765 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1765
  have eq1767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq786 eq1766
    | exact resolve eq1766 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq1766
  have eq1768 : False := by grind
  exact eq1768

/-- `Equation1460`: `x = (x ◇ y) ◇ (y ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_pxy_pyx_Equation1460 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1460 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq174 : x ≠ (M.op x y) ∨ y = (k x y) := by
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
  have eq175 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : x = (M.op (M.op x y) (M.op y (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x) (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq226 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) := by
    first
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq289 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq181 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq181
    | (have j0 := eq181 y X0 x
       grind)
    | exact resolve eq181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq181
    | (have j0 := eq181 (σ y) X0 (σ x)
       grind)
    | exact resolve eq181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq289 eq181
    | exact resolve eq181 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq289
  have eq540 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq547 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2429 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq540
       grind)
    | exact superpose eq540 eq39
    | exact resolve eq39 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq2430 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2429
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2429
    | exact resolve eq2429 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429
  have eq2432 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq2430
    | exact resolve eq2430 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430
  have eq2662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2432 eq547
    | exact resolve eq547 eq2432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2432
  have eq2669 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq2662
       have r₂ := eq27
       grind)
    | exact resolve eq2662 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2683 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2669 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2669
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2669
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2669
       grind)
    | exact resolve eq13 eq2669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2669
  have eq2705 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq2683
  have eq2787 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2705 eq107
    | exact resolve eq107 eq2705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq2705
  have eq2794 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq2787
    | exact resolve eq2787 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2787
  have eq2797 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq2794
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq2794
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq2794
       have r₂ := eq13 y x
       grind)
    | exact resolve eq2794 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794
  have eq2801 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq540
       have i₂ := eq2797
       grind)
    | exact superpose eq2797 eq540
    | exact resolve eq540 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq2802 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq2797
       grind)
    | exact superpose eq2797 eq36
    | exact resolve eq36 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2797
  have eq2804 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2801
  have eq2807 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2802
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2802
    | exact resolve eq2802 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802
  have eq2817 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2804
       grind)
    | exact superpose eq2804 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2804
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2804
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2804
       grind)
    | exact resolve eq12 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq2841 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2817
  have eq2845 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2841
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2841
    | exact resolve eq2841 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2841
  have eq2846 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2845
  have eq2848 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2846
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2846
    | exact resolve eq2846 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846
  have eq2854 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2807 eq547
    | exact resolve eq547 eq2807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq2807
  have eq2858 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2854
  have eq2938 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2848
       grind)
    | exact superpose eq2848 eq40
    | exact resolve eq40 eq2848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2848
  have eq2939 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2938
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2938
    | exact resolve eq2938 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq2941 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2939
    | exact resolve eq2939 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939
  have eq2952 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2858 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2858
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2858
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2858
       grind)
    | exact resolve eq12 eq2858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq2976 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2952
  have eq2980 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2976
    | exact resolve eq2976 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq2981 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2980
  have eq2983 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2981
    | exact resolve eq2981 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981
  have eq2985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2941 eq2983
    | exact resolve eq2983 eq2941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2941 eq2983
  have eq2986 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2985
       have r₂ := eq27
       grind)
    | exact resolve eq2985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985
  have eq2988 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2986 eq175
    | (have r₁ := eq175
       have r₂ := eq2986
       grind)
    | exact resolve eq175 eq2986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2986
  have eq3011 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2988
  have eq3016 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3011 eq90
    | exact resolve eq90 eq3011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3011
  have eq3019 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq3016
    | exact resolve eq3016 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3016
  have eq3022 : y = (k x y) := by
    first
    | (have r₁ := eq3019
       have r₂ := eq174
       grind)
    | exact resolve eq3019 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq3019
  have eq3027 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq3022
       grind)
    | exact superpose eq3022 eq35
    | exact resolve eq35 eq3022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3030 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3027
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3027
    | exact resolve eq3027 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3027
  have eq3404 : y ≠ y ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq606 y x
       have i₂ := eq3022
       grind)
    | exact superpose eq3022 eq606
    | (have j0 := eq606 y x
       grind)
    | (have r₁ := eq606 y x
       have r₂ := eq3022
       grind)
    | exact resolve eq606 eq3022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3409 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3030 eq606
    | (have j0 := eq606 (σ y) (σ x)
       grind)
    | (have r₁ := eq606 (σ y) (σ x)
       have r₂ := eq3030
       grind)
    | exact resolve eq606 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq3419 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3409
  have eq3423 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq3404
  have eq3425 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3419
    | exact resolve eq3419 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq3426 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3423
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3423
    | exact resolve eq3423 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3423
  have eq3435 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq3426
       grind)
    | exact superpose eq3426 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3426
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3426
       grind)
    | exact resolve eq12 eq3426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3461 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq3435
  have eq3465 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3461
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3461
    | exact resolve eq3461 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3461
  have eq3466 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq3465
  have eq3467 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3466
       have i₂ := eq3022
       grind)
    | exact superpose eq3022 eq3466
    | exact resolve eq3466 eq3022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022 eq3466
  have eq3468 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3467
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3467
    | exact resolve eq3467 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3467
  have eq3477 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq187
       have i₂ := eq3468
       grind)
    | exact superpose eq3468 eq187
    | exact resolve eq187 eq3468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq3492 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3426
       have i₂ := eq3468
       grind)
    | exact superpose eq3468 eq3426
    | exact resolve eq3426 eq3468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426 eq3468
  have eq3493 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq3492
  have eq3507 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313 eq3477
    | exact resolve eq3477 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq3477
  have eq3515 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3493 eq3507
    | exact resolve eq3507 eq3493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3493 eq3507
  have eq3516 : x = (M.op x y) := by grind
  clear eq3515
  have eq3526 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq3516
       grind)
    | exact superpose eq3516 eq22
    | exact resolve eq22 eq3516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3516
  have eq3556 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3526 eq20
    | exact resolve eq20 eq3526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3526
  have eq3816 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3425 eq295
    | exact resolve eq295 eq3425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq3817 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3425 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3425
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3425
       grind)
    | exact resolve eq12 eq3425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3843 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3817
  have eq3847 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3843
    | exact resolve eq3843 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843
  have eq3848 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq3847
  have eq3849 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3030 eq3848
    | exact resolve eq3848 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3030 eq3848
  have eq3850 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3849
    | exact resolve eq3849 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3849
  have eq3859 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3850 eq226
    | exact resolve eq226 eq3850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq3874 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq3877 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3425 eq3859
    | exact resolve eq3859 eq3425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3425 eq3859
  have eq4095 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3850 eq3816
    | exact resolve eq3816 eq3850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816 eq3850
  have eq4139 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4095
       have r₂ := eq3874
       grind)
    | exact resolve eq4095 eq3874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095
  have eq4141 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3877 eq4139
    | exact resolve eq4139 eq3877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3877 eq4139
  have eq4143 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4141
       have r₂ := eq3874
       grind)
    | exact resolve eq4141 eq3874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874 eq4141
  have eq4145 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4143 eq27
    | exact resolve eq27 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4143
  have eq4173 : False := by grind
  exact eq4173

/-- `Equation1460`: `x = (x ◇ y) ◇ (y ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxx_pxy_pyx_Equation1460 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1460 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq51 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op x y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) X2 (M.op x x)
       have i₂ := eq14 X0 X2 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) ≠ X0 ∨ (k (M.op X1 (M.op X2 X3)) (M.op X0 X1)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X1 (M.op X2 X3)) (M.op X0 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X1 (M.op X2 X3)) (M.op X0 X1)
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op X2 X3)) (M.op (M.op X1 (M.op X2 X3)) X1)
       have r₂ := eq14 (M.op X1 (M.op X2 X3)) X1 X2 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq80 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq85 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq85
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (k x (k y x))) = (k (σ x) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq36 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq36
    | exact resolve eq36 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq114 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq132 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
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
  clear eq38
  have eq143 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq151 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq134
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq134
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq134 eq16
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq151
  have eq211 : ∀ X0 : G, x = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq224 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq284 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq215 eq56
    | exact resolve eq56 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq211 eq56
    | exact resolve eq56 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq224 eq56
    | exact resolve eq56 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y X0 x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) X0 (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq304 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (k (M.op X1 X2) (M.op X0 X1)) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq56 X2 X0 X1
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 (M.op X1 X2) (M.op X0 X1)
       grind)
    | (have r₁ := eq13 (M.op X2 X0) (M.op (M.op X2 X0) X2)
       have r₂ := eq56 X0 (M.op X2 X0) X2
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq230 eq54
    | exact resolve eq54 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq230 eq56
    | exact resolve eq56 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq338 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 (M.op X1 X2))
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 X1 (M.op X0 (M.op X1 X2))
       grind)
    | (have r₁ := eq13 X1 (M.op X1 (M.op X1 X2))
       have r₂ := eq57 X1 X1 X2
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq54
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X2 (M.op X0 (M.op X1 X3)) X1
       have i₂ := eq57 X1 X0 X3
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq418 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq542 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq56
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq56 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq581 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (k (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 (M.op X0 (M.op X1 X2)) X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq609 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq392
    | exact resolve eq392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq705 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq418 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq418
    | (have j0 := eq418 x X0
       grind)
    | exact resolve eq418 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq1496 : (k x (k (M.op x y) x)) = (τ (k (σ x) (k (σ (M.op x y)) (σ x)))) := by
    first
    | exact superpose eq143 eq705
    | exact resolve eq705 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1498 : (k x (k (M.op x y) (M.op x y))) = (τ (k (σ x) (k (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq157 eq705
    | exact resolve eq705 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1502 : (k x (k y x)) = (τ (k (σ x) (k (σ y) (σ x)))) := by
    first
    | exact superpose eq98 eq705
    | exact resolve eq705 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1504 : (k x (k y (M.op x y))) = (τ (k (σ x) (k (σ y) (σ (M.op x y))))) := by
    first
    | exact superpose eq114 eq705
    | exact resolve eq705 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq705
  have eq2601 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq338 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq6105 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq304 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq6555 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq80
    | (have j0 := eq80 x
       grind)
    | exact resolve eq80 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq6580 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6555
  have eq6588 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6580
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6580
    | exact resolve eq6580 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6580
  have eq6602 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6588
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6588 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6588
  have eq6606 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6602 eq50
    | exact resolve eq50 eq6602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq6745 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq81 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq81
    | (have j0 := eq81 y
       grind)
    | exact resolve eq81 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq6768 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6745
  have eq6773 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6768
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq6768
    | exact resolve eq6768 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq6768
  have eq6794 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6773
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6773 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6773
  have eq6813 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6794 eq107
    | exact resolve eq107 eq6794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq7060 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq135
    | (have j0 := eq135 (M.op x y)
       grind)
    | exact resolve eq135 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq7082 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq7060
  have eq7086 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq7082
    | exact resolve eq7082 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq7082
  have eq7114 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq7086
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq7086 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7086
  have eq7150 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq7114 eq157
    | exact resolve eq157 eq7114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq8299 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6602 eq92
    | exact resolve eq92 eq6602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq8538 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8539 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8538
    | exact resolve eq8538 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8538
  have eq8550 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8539
       have r₂ := eq28
       grind)
    | exact resolve eq8539 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8539
  have eq8552 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8550
    | exact resolve eq8550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8550
  have eq8561 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq8552 eq318
    | exact resolve eq318 eq8552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8562 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8552 eq299
    | exact resolve eq299 eq8552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8552
  have eq9106 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq546 (τ X1) (τ X0)
       have i₂ := eq609 X1 X0
       grind)
    | exact superpose eq609 eq546
    | (have j0 := eq546 (τ X1) (τ X0)
       grind)
    | exact resolve eq546 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq609
  have eq9291 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9106 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq9106
    | (have j0 := eq9106 X0 X1
       grind)
    | exact resolve eq9106 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9106
  have eq9382 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9291 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9291
    | (have j0 := eq9291 X0 X1
       grind)
    | exact resolve eq9291 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9291
  have eq9470 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9382 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9382
    | (have j0 := eq9382 X0 X1
       grind)
    | exact resolve eq9382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9382
  have eq9553 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9470 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9470
    | (have j0 := eq9470 X0 X1
       grind)
    | exact resolve eq9470 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9470
  have eq9632 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9553 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9553
    | (have j0 := eq9553 X0 X1
       grind)
    | exact resolve eq9553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9553
  have eq9652 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9632 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq9632
    | (have j0 := eq9632 X0 X1
       grind)
    | exact resolve eq9632 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9632
  have eq10289 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X0)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq581 X0 X1 X2
       have i₂ := eq343 (M.op X0 (M.op X1 X2)) X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq581 X1 x y
       have i₂ := eq343 (M.op X1 (M.op x y)) X1 X2
       grind)
    | exact superpose eq343 eq581
    | exact resolve eq581 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq581
  have eq10374 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op x y))) = (k (M.op X0 (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10289 X0 X0 X1
       have i₂ := eq57 X0 X0 X1
       grind)
    | exact superpose eq57 eq10289
    | exact resolve eq10289 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10289
  have eq11618 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8561 eq8562
    | exact resolve eq8562 eq8561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8561 eq8562
  have eq11625 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11618
  have eq11639 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11625 eq6813
    | exact resolve eq6813 eq11625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11625
  have eq11691 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq11639
    | exact resolve eq11639 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11639
  have eq12513 : ∀ X0 : G, (M.op (M.op X0 x) y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq56 x X0 x
       have i₂ := eq11691
       grind)
    | exact superpose eq11691 eq56
    | exact resolve eq56 eq11691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18206 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6794 eq108
    | exact resolve eq108 eq6794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq6794
  have eq19522 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7114 eq158
    | exact resolve eq158 eq7114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq7114
  have eq19526 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq12513 x
       have i₂ := eq11691
       grind)
    | exact superpose eq11691 eq12513
    | exact resolve eq12513 eq11691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11691 eq12513
  have eq19562 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19526
  have eq19578 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq19562
       grind)
    | exact superpose eq19562 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq19562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19590 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19578
  have eq19646 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq19590
       grind)
    | exact superpose eq19590 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq19590
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19590
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19590
       grind)
    | exact resolve eq13 eq19590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19674 : x ≠ y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19590
  have eq19675 : y = (k y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19646
  have eq19791 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19562
       have i₂ := eq19675
       grind)
    | exact superpose eq19675 eq19562
    | exact resolve eq19562 eq19675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19562 eq19675
  have eq19814 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19791
  have eq19827 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19814
       have r₂ := eq19674
       grind)
    | exact resolve eq19814 eq19674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19674 eq19814
  have eq19859 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq19869 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq56 X0 y y
       have i₂ := eq19827
       grind)
    | exact superpose eq19827 eq56
    | exact resolve eq56 eq19827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19871 : ∀ X0 : G, (M.op (M.op X0 x) y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq57 y X0 y
       have i₂ := eq19827
       grind)
    | exact superpose eq19827 eq57
    | exact resolve eq57 eq19827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq19876 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 y y X1
       have i₂ := eq19827
       grind)
    | exact superpose eq19827 eq345
    | exact resolve eq345 eq19827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq19893 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19859
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19859
    | exact resolve eq19859 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19859
  have eq20051 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19869 y
       have i₂ := eq19827
       grind)
    | exact superpose eq19827 eq19869
    | exact resolve eq19869 eq19827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19827 eq19869
  have eq20126 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20051
  have eq20148 : x ≠ y ∨ y = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq20126
       grind)
    | exact superpose eq20126 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq20126
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20126
       grind)
    | exact resolve eq13 eq20126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23312 : (M.op y y) = (k y (M.op y x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2601 y x
       have i₂ := eq19876 y x
       grind)
    | exact superpose eq19876 eq2601
    | exact resolve eq2601 eq19876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19876
  have eq24201 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19893
       grind)
    | exact superpose eq19893 eq45
    | exact resolve eq45 eq19893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19893
  have eq24233 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq24201
    | exact resolve eq24201 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24201
  have eq25370 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8299
       have i₂ := eq20126
       grind)
    | exact superpose eq20126 eq8299
    | exact resolve eq8299 eq20126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20126
  have eq25379 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq8299
       grind)
    | exact superpose eq8299 eq16
    | exact resolve eq16 eq8299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25447 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6606 eq25379
    | exact resolve eq25379 eq6606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25379
  have eq25451 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25370
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25370
    | exact resolve eq25370 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25370
  have eq25462 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq25447
       have r₂ := eq13 x x
       grind)
    | exact resolve eq25447 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25447
  have eq25465 : (τ (σ y)) = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25451 eq6606
    | exact resolve eq6606 eq25451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25451
  have eq25526 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq25465
    | exact resolve eq25465 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq25465
  have eq25527 : y = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq25526
       have r₂ := eq20148
       grind)
    | exact resolve eq25526 eq20148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20148 eq25526
  have eq25529 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq25527
       grind)
    | exact superpose eq25527 eq44
    | exact resolve eq44 eq25527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq25527
  have eq25567 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6602 eq25529
    | exact resolve eq25529 eq6602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6602 eq25529
  have eq25582 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25567
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25567
    | exact resolve eq25567 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25567
  have eq25612 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25582 eq303
    | exact resolve eq303 eq25582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq25624 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25582 eq56
    | exact resolve eq56 eq25582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25582
  have eq25656 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq25612
    | exact resolve eq25612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25612
  have eq26109 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq18206
       grind)
    | exact superpose eq18206 eq16
    | exact resolve eq16 eq18206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26179 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6813 eq26109
    | exact resolve eq26109 eq6813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26109
  have eq26194 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq26179
       have r₂ := eq13 y y
       grind)
    | exact resolve eq26179 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26179
  have eq26667 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq19522 eq16
    | exact resolve eq16 eq19522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19522
  have eq26739 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7150 eq26667
    | exact resolve eq26667 eq7150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7150 eq26667
  have eq26752 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq26739
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq26739 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26739
  have eq34502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25656 eq24233
    | exact resolve eq24233 eq25656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24233 eq25656
  have eq34511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq34502
  have eq34515 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq34511
       have r₂ := eq28
       grind)
    | exact resolve eq34511 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34511
  have eq34708 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq34515 eq25624
    | exact resolve eq25624 eq34515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25624 eq34515
  have eq34743 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq34708
  have eq34761 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq34743
    | exact resolve eq34743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34743
  have eq34762 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34761
  have eq34773 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23312
       have i₂ := eq34762
       grind)
    | exact superpose eq34762 eq23312
    | exact resolve eq23312 eq34762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23312
  have eq34782 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19871 y
       have i₂ := eq34762
       grind)
    | exact superpose eq34762 eq19871
    | exact resolve eq19871 eq34762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19871 eq34762
  have eq34818 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34782
  have eq34823 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34773
  have eq34835 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34818
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34818
    | exact resolve eq34818 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34818
  have eq34836 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq34835
  have eq34841 : (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34823
       have r₂ := eq67
       grind)
    | exact resolve eq34823 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34823
  have eq34845 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34836 eq68
    | (have r₁ := eq68
       have r₂ := eq34836
       grind)
    | exact resolve eq68 eq34836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq34846 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34836 eq224
    | exact resolve eq224 eq34836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34836
  have eq34862 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq34845
  have eq34873 : (k (σ x) (k (σ y) (σ x))) = (σ (k x (M.op y y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq34841
       grind)
    | exact superpose eq34841 eq95
    | exact resolve eq95 eq34841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq34884 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq542 y x X0
       have i₂ := eq34841
       grind)
    | exact superpose eq34841 eq542
    | (have j0 := eq542 y x x
       grind)
    | exact resolve eq542 eq34841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq34841
  have eq34897 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34884 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34884
    | (have j0 := eq34884 X0
       grind)
    | exact resolve eq34884 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34884
  have eq34905 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34897 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34897
    | (have j0 := eq34897 X0
       grind)
    | exact resolve eq34897 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34897
  have eq34913 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34905 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34905
    | (have j0 := eq34905 X0
       grind)
    | exact resolve eq34905 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34905
  have eq34919 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34913 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34913
    | (have j0 := eq34913 X0
       grind)
    | exact resolve eq34913 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34913
  have eq34924 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34919 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34919
    | (have j0 := eq34919 X0
       grind)
    | exact resolve eq34919 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34919
  have eq34932 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34924 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34924
    | (have j0 := eq34924 X0
       grind)
    | exact resolve eq34924 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34924
  have eq34934 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq34932
    | (have j0 := eq34932 X0
       grind)
    | exact resolve eq34932 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34932
  have eq34935 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq34934 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34934
  have eq34938 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34846 eq34846
    | exact resolve eq34846 eq34846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34984 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X1)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq34846 eq290
    | exact resolve eq290 eq34846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34846
  have eq35052 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq34938
  have eq35063 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq318 eq34984
    | (have j0 := eq34984 (σ y)
       grind)
    | exact resolve eq34984 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34984
  have eq35127 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35052 eq299
    | exact resolve eq299 eq35052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35052
  have eq35449 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34862 eq98
    | exact resolve eq98 eq34862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35450 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34862 eq101
    | exact resolve eq101 eq34862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq34862
  have eq35471 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq35450
  have eq35482 : (k y x) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6813 eq35449
    | exact resolve eq35449 eq6813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35449
  have eq35682 : (k y x) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq35482
       grind)
    | exact superpose eq35482 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq35482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35694 : (k y x) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq35682
  have eq35716 : (k y x) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq35694
       have r₂ := eq67
       grind)
    | exact resolve eq35694 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35694
  have eq35983 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op x y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35063 eq10374
    | (have j0 := eq10374 (σ x) (σ y)
       grind)
    | exact resolve eq10374 eq35063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35063
  have eq36168 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq316 eq35983
    | exact resolve eq35983 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq35983
  have eq37755 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq35716
       grind)
    | exact superpose eq35716 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq35716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35716
  have eq37768 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq37755
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37755
    | exact resolve eq37755 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37755
  have eq37776 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq37768
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37768
    | exact resolve eq37768 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37768
  have eq51440 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq35471 eq6813
    | exact resolve eq6813 eq35471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35471
  have eq51548 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq51440
    | exact resolve eq51440 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51440
  have eq57309 : (k (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35127 eq36168
    | exact resolve eq36168 eq35127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35127 eq36168
  have eq57332 : (k (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq57309
  have eq57344 : (k y x) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57332 eq98
    | exact resolve eq98 eq57332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57332
  have eq441241 : ∀ X0 X1 : G, (σ (M.op y y)) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq34935 eq56
    | exact resolve eq56 eq34935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34935
  have eq441323 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq290 eq441241
    | exact resolve eq441241 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq441241
  have eq441361 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq441323
       grind)
    | exact superpose eq441323 eq16
    | exact resolve eq16 eq441323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441323
  have eq443109 : (M.op (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18206
       have i₂ := eq441361
       grind)
    | exact superpose eq441361 eq18206
    | exact resolve eq18206 eq441361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18206 eq441361
  have eq443314 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq443109
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq443109
    | exact resolve eq443109 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443109
  have eq459958 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq443314 eq56
    | exact resolve eq56 eq443314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443314
  have eq460036 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq224 eq459958
    | exact resolve eq459958 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq459958
  have eq461079 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq460036 eq318
    | exact resolve eq318 eq460036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq461080 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq460036 eq299
    | exact resolve eq299 eq460036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461098 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq461109 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = X0 ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq460036 eq56
    | exact resolve eq56 eq460036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460036
  have eq461182 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq461098
    | exact resolve eq461098 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461098
  have eq461183 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq461182
  have eq478211 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq461079 eq461080
    | exact resolve eq461080 eq461079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461079 eq461080
  have eq478257 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq478211
  have eq479234 : (τ (σ x)) = (k y y) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq478257 eq6813
    | exact resolve eq6813 eq478257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6813 eq478257
  have eq479444 : x = (k y y) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq479234
    | exact resolve eq479234 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479234
  have eq526441 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq56 X0 y y
       have i₂ := eq37776
       grind)
    | exact superpose eq37776 eq56
    | exact resolve eq56 eq37776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37776
  have eq526516 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq211 eq526441
    | exact resolve eq526441 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526441
  have eq526609 : y ≠ y ∨ y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq526516
       grind)
    | exact superpose eq526516 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq526516
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq526516
       grind)
    | exact resolve eq13 eq526516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526516
  have eq526663 : y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq526609
  have eq527841 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq51548
       have i₂ := eq526663
       grind)
    | exact superpose eq526663 eq51548
    | exact resolve eq51548 eq526663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51548 eq526663
  have eq527951 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq527841
  have eq528141 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8299
       have i₂ := eq527951
       grind)
    | exact superpose eq527951 eq8299
    | exact resolve eq8299 eq527951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8299
  have eq528160 : (k y x) = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  have eq528171 : ∀ X0 : G, (M.op (M.op X0 x) y) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq56 x X0 x
       have i₂ := eq527951
       grind)
    | exact superpose eq527951 eq56
    | exact resolve eq56 eq527951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq527951
  have eq528228 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq528141
  have eq528248 : y = (M.op x y) ∨ (k y x) = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq528160
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq528160
    | exact resolve eq528160 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528160
  have eq528249 : (k y x) = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq528248
  have eq528256 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq528228
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq528228
    | exact resolve eq528228 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528228
  have eq530668 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq528256 eq299
    | exact resolve eq299 eq528256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq528256
  have eq532371 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq530668 eq57344
    | exact resolve eq57344 eq530668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57344 eq530668
  have eq532719 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq532371
  have eq532801 : x = (k y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq532719
    | exact resolve eq532719 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532719
  have eq542626 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq532801
       have i₂ := eq528249
       grind)
    | exact superpose eq528249 eq532801
    | exact resolve eq532801 eq528249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528249 eq532801
  have eq542666 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq542626
  have eq542780 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq528171 y
       have i₂ := eq542666
       grind)
    | exact superpose eq542666 eq528171
    | exact resolve eq528171 eq542666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528171 eq542666
  have eq542843 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq542780
  have eq542866 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq542843
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq542843
    | exact resolve eq542843 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542843
  have eq542867 : y = (M.op x y) ∨ x = y := by grind
  clear eq542866
  have eq542872 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq542867 eq21
    | exact resolve eq21 eq542867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542877 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq542867 eq67
    | (have r₁ := eq67
       have r₂ := eq542867
       grind)
    | exact resolve eq67 eq542867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542923 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq542867 eq211
    | exact resolve eq211 eq542867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542924 : ∀ X0 : G, (M.op (M.op X0 y) x) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq542867 eq215
    | exact resolve eq215 eq542867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543174 : (k y x) = (M.op y y) ∨ x = y := by grind
  clear eq542877
  have eq543323 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq542872
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq542872
    | exact resolve eq542872 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542872
  have eq544182 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = y := by
    first
    | exact superpose eq543323 eq98
    | exact resolve eq98 eq543323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq544226 : (k x (k y x)) = (τ (k (σ x) (k (σ (M.op x y)) (σ x)))) ∨ x = y := by
    first
    | exact superpose eq543323 eq1502
    | exact resolve eq1502 eq543323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq544228 : (k x (k y (M.op x y))) = (τ (k (σ x) (k (σ (M.op x y)) (σ (M.op x y))))) ∨ x = y := by
    first
    | exact superpose eq543323 eq1504
    | exact resolve eq1504 eq543323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq544961 : (k x (k y (M.op x y))) = (k x (k (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1498 eq544228
    | exact resolve eq544228 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498 eq544228
  have eq544963 : (k x (k y x)) = (k x (k (M.op x y) x)) ∨ x = y := by
    first
    | exact superpose eq1496 eq544226
    | exact resolve eq544226 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544226
  have eq544999 : (k y x) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq143 eq544182
    | exact resolve eq544182 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq544182
  have eq545968 : x = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq542923 (M.op y x)
       have i₂ := eq542923 x
       grind)
    | exact superpose eq542923 eq542923
    | exact resolve eq542923 eq542923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546081 : ∀ X1 : G, (M.op x y) = (M.op x (M.op x X1)) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq287 (M.op y x) X1
       have i₂ := eq542923 x
       grind)
    | exact superpose eq542923 eq287
    | exact resolve eq287 eq542923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq542923
  have eq546173 : x = (M.op y x) ∨ x = y := by grind
  clear eq545968
  have eq546192 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq546081 x
       have i₂ := eq284 x x
       grind)
    | (have i₁ := eq546081 y
       have i₂ := eq284 x x
       grind)
    | exact superpose eq284 eq546081
    | (have j0 := eq546081 y
       grind)
    | exact resolve eq546081 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq546081
  have eq547067 : y = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq296 y
       have i₂ := eq546173
       grind)
    | exact superpose eq546173 eq296
    | exact resolve eq296 eq546173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq546173
  have eq547967 : (M.op (M.op x (M.op x y)) (M.op x y)) = (k (M.op x (M.op x y)) x) ∨ x = y := by
    first
    | exact superpose eq546192 eq10374
    | exact resolve eq10374 eq546192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10374 eq546192
  have eq552335 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq6105 x y
       have i₂ := eq542924 x
       grind)
    | exact superpose eq542924 eq6105
    | exact resolve eq6105 eq542924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6105 eq542924
  have eq552421 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq552335
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq552335
    | exact resolve eq552335 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552335
  have eq562596 : (k y x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq552421 eq544999
    | exact resolve eq544999 eq552421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544999
  have eq562636 : (k y x) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq562596
  have eq572812 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq543174
       have i₂ := eq562636
       grind)
    | exact superpose eq562636 eq543174
    | exact resolve eq543174 eq562636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543174 eq562636
  have eq572852 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq572812
  have eq582265 : (M.op y y) = (k (M.op x y) (M.op (M.op x y) (M.op y y))) ∨ x = y := by
    first
    | exact superpose eq572852 eq2601
    | exact resolve eq2601 eq572852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601 eq572852
  have eq582312 : (M.op y y) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq211 eq582265
    | exact resolve eq582265 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq582265
  have eq840952 : (k x (k y x)) = (k x (M.op (M.op x y) (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq552421 eq544963
    | exact resolve eq544963 eq552421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544963 eq552421
  have eq840998 : (k x (k y x)) = (k x (M.op (M.op x y) (M.op x y))) ∨ x = y := by grind
  clear eq840952
  have eq867411 : (k y x) = (M.op y (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq547067 eq547967
    | exact resolve eq547967 eq547067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547067 eq547967
  have eq867467 : (k y x) = (M.op y (M.op x y)) ∨ x = y := by grind
  clear eq867411
  have eq1004742 : (k x (M.op y (M.op x y))) = (k x (M.op (M.op x y) (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq840998
       have i₂ := eq867467
       grind)
    | exact superpose eq867467 eq840998
    | exact resolve eq840998 eq867467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840998 eq867467
  have eq1004813 : (k x (M.op y (M.op x y))) = (k x (M.op (M.op x y) (M.op x y))) ∨ x = y := by grind
  clear eq1004742
  have eq1368126 : (k x (M.op y (M.op x y))) = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ x = y := by
    first
    | exact superpose eq1004813 eq11
    | (have j0 := eq11 x (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq11 eq1004813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004813
  have eq1368201 : (M.op x y) = (k x (M.op y (M.op x y))) ∨ x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ x = y := by
    first
    | exact superpose eq215 eq1368126
    | exact resolve eq1368126 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368126
  have eq1368240 : x = (M.op x y) ∨ (M.op x y) = (k x (M.op y (M.op x y))) ∨ x = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ x = y := by
    first
    | exact superpose eq54 eq1368201
    | exact resolve eq1368201 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368201
  have eq1368257 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op y (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq215 eq1368240
    | exact resolve eq1368240 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368240
  have eq1368258 : (M.op x y) = (k x (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1368257
  have eq1368281 : y = (k x (M.op y y)) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq542867 eq1368258
    | exact resolve eq1368258 eq542867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368258
  have eq1368344 : y = (k x (M.op y y)) ∨ x = y := by grind
  clear eq1368281
  have eq1368525 : (σ y) = (k (σ x) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq34873
       have i₂ := eq1368344
       grind)
    | exact superpose eq1368344 eq34873
    | exact resolve eq34873 eq1368344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34873 eq1368344
  have eq1368629 : (σ y) = (k (σ x) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1368525
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1368525
    | exact resolve eq1368525 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368525
  have eq1377990 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq543323 eq1368629
    | exact resolve eq1368629 eq543323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368629
  have eq1378083 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1377990
  have eq1378086 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ x))) ∨ x = y := by
    first
    | (have r₁ := eq1378083
       have r₂ := eq28
       grind)
    | exact resolve eq1378083 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378083
  have eq1378092 : (τ (σ (M.op x y))) = (k x (k (M.op x y) x)) ∨ x = y := by
    first
    | exact superpose eq1378086 eq1496
    | exact resolve eq1496 eq1378086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496 eq1378086
  have eq1378131 : (M.op x y) = (k x (k (M.op x y) x)) ∨ x = y := by
    first
    | exact superpose eq31 eq1378092
    | exact resolve eq1378092 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378092
  have eq1382215 : (M.op x y) = (k x (M.op y y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq582312 eq1378131
    | exact resolve eq1378131 eq582312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582312 eq1378131
  have eq1382287 : (M.op x y) = (k x (M.op y y)) ∨ x = y := by grind
  clear eq1382215
  have eq1897352 : x = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26194
       have i₂ := eq479444
       grind)
    | exact superpose eq479444 eq26194
    | exact resolve eq26194 eq479444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479444
  have eq1897384 : (k y x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35482
       have i₂ := eq26194
       grind)
    | exact superpose eq26194 eq35482
    | exact resolve eq35482 eq26194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35482
  have eq1897665 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq1897384
       have r₂ := eq67
       grind)
    | exact resolve eq1897384 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1897384
  have eq1897878 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq1897665
       grind)
    | exact superpose eq1897665 eq76
    | exact resolve eq76 eq1897665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1897665
  have eq1982684 : x ≠ (k x (k y (M.op x y))) ∨ x = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ x = (M.op (k (M.op x y) (M.op x y)) x) ∨ x = y := by
    first
    | exact superpose eq544961 eq9652
    | (have j0 := eq9652 x (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq9652 eq544961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9652 eq544961
  have eq1983696 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x ≠ (k x (k y (M.op x y))) ∨ x = (M.op (k (M.op x y) (M.op x y)) x) ∨ x = y := by
    first
    | exact superpose eq26752 eq1982684
    | exact resolve eq1982684 eq26752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982684
  have eq1984019 : x = (M.op x y) ∨ x ≠ (k x (k y (M.op x y))) ∨ x = (M.op (k (M.op x y) (M.op x y)) x) ∨ x = y := by
    first
    | exact superpose eq54 eq1983696
    | exact resolve eq1983696 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1983696
  have eq1984194 : x = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x y) ∨ x ≠ (k x (k y (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq26752 eq1984019
    | exact resolve eq1984019 eq26752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26752 eq1984019
  have eq1984255 : x = (M.op x y) ∨ x = (M.op x y) ∨ x ≠ (k x (k y (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq215 eq1984194
    | exact resolve eq1984194 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq1984194
  have eq1984256 : x ≠ (k x (k y (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1984255
  have eq2047367 : x ≠ (k x (k y y)) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq542867 eq1984256
    | exact resolve eq1984256 eq542867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542867 eq1984256
  have eq2047395 : x ≠ (k x (k y y)) ∨ x = y := by grind
  clear eq2047367
  have eq2047402 : x ≠ (k x (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq2047395
       have i₂ := eq26194
       grind)
    | exact superpose eq26194 eq2047395
    | exact resolve eq2047395 eq26194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26194 eq2047395
  have eq2048322 : x ≠ (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq2047402
       have i₂ := eq1382287
       grind)
    | exact superpose eq1382287 eq2047402
    | exact resolve eq2047402 eq1382287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382287 eq2047402
  have eq2048328 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq2048322
  have eq3784855 : (σ x) = (k (σ y) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1897878
       have i₂ := eq1897352
       grind)
    | exact superpose eq1897352 eq1897878
    | exact resolve eq1897878 eq1897352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897352 eq1897878
  have eq3785522 : (σ x) = (k (σ y) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3784855
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3784855
    | exact resolve eq3784855 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3784855
  have eq4074433 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3785522 eq461183
    | exact resolve eq461183 eq3785522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461183 eq3785522
  have eq4074738 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq4074433
  have eq4086103 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4074738 eq461109
    | exact resolve eq461109 eq4074738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461109 eq4074738
  have eq4086371 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4086103
  have eq4086434 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq4086371
    | exact resolve eq4086371 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086371
  have eq4086435 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq4086434
  have eq4086479 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4086435 eq15
    | exact resolve eq15 eq4086435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086435
  have eq4087328 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4086479
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4086479
    | exact resolve eq4086479 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086479
  have eq4087329 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq4087328
  have eq4087378 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4087329 eq28
    | exact resolve eq28 eq4087329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4087329
  have eq4087908 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq543323 eq4087378
    | (have r₁ := eq4087378
       have r₂ := eq543323
       grind)
    | exact resolve eq4087378 eq543323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543323 eq4087378
  have eq4087909 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq4087908
  have eq4087911 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq4087909 eq29
    | exact resolve eq29 eq4087909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4087909
  have eq4090675 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq4087911
    | exact resolve eq4087911 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4087911
  have eq4090814 : x = y := by
    first
    | (have r₁ := eq4090675
       have r₂ := eq2048328
       grind)
    | exact resolve eq4090675 eq2048328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048328 eq4090675
  have eq4091962 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq4090814
       grind)
    | exact superpose eq4090814 eq19
    | exact resolve eq19 eq4090814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4091963 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq4090814
       grind)
    | exact superpose eq4090814 eq25
    | exact resolve eq25 eq4090814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4090814
  have eq4093403 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4091963
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4091963
    | exact resolve eq4091963 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4091963
  have eq4093590 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4093403 eq27
    | exact resolve eq27 eq4093403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4093403
  have eq4099589 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4093590 eq6606
    | exact resolve eq6606 eq4093590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6606 eq4093590
  have eq4100166 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4099589
       have i₂ := eq25462
       grind)
    | exact superpose eq25462 eq4099589
    | exact resolve eq4099589 eq25462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25462 eq4099589
  have eq4100227 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4100166
       have i₂ := eq4091962
       grind)
    | exact superpose eq4091962 eq4100166
    | exact resolve eq4100166 eq4091962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4091962 eq4100166
  have eq4100340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4100227 eq15
    | exact resolve eq15 eq4100227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100227
  have eq4101436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq4100340
    | exact resolve eq4100340 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq4100340
  have eq4101759 : False := by grind
  exact eq4101759

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_y_pxy_x_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq62 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq119 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq9
    | exact resolve eq9 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X0
       have i₂ := eq119 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq119 eq9
    | exact resolve eq9 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq130 X0
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq130
    | exact resolve eq130 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq138 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq122 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq122
    | exact resolve eq122 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq643 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X2 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq68
    | exact resolve eq68 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq847 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq643 X0 x X1
       grind)
    | exact superpose eq643 eq9
    | exact resolve eq9 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq897 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq847 X0 X0 x
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq847
    | exact resolve eq847 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq942 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq897 (σ X1) X1
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq897
    | exact resolve eq897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq2061 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq942 (M.op X0 (k X0 X0)) X1
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq942
    | exact resolve eq942 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq2244 : ∀ X0 X1 : G, (σ (M.op X0 (k X0 X0))) = (M.op (σ (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0)))) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq138 (M.op X0 (k X0 X0)) (M.op (σ X0) X1)
       have i₂ := eq2061 X0 X1
       grind)
    | exact superpose eq2061 eq138
    | exact resolve eq138 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq2061
  have eq2282 : ∀ X0 X1 : G, (σ (M.op X0 (k X0 X0))) = (M.op (σ X0) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2244 X0 X1
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq2244
    | exact resolve eq2244 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq2244
  have eq2295 : ∀ X0 : G, (σ (M.op X0 (k X0 X0))) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2282 X0 x
       have i₂ := eq67 (σ X0) (σ X0) x
       grind)
    | exact superpose eq67 eq2282
    | exact resolve eq2282 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2282
  have eq2300 : ∀ X0 : G, (M.op (σ X0) (k (σ X0) (σ X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2295 X0
       have i₂ := eq119 (σ X0)
       grind)
    | exact superpose eq119 eq2295
    | exact resolve eq2295 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2304 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2300 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2300
    | exact resolve eq2300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2300
  have eq8534 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8535 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8534 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq8534
    | (have j0 := eq8534 X0 X1
       grind)
    | exact resolve eq8534 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq8534
  have eq8763 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8535 (σ x) (σ y)
       grind)
    | exact superpose eq8535 eq16
    | (have j1 := eq8535 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq8535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8806 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq8763
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8763
    | exact resolve eq8763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8763
  have eq8816 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq8806
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq8806
    | exact resolve eq8806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8806
  have eq9675 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq8816
       have i₂ := eq8535 x y
       grind)
    | exact superpose eq8535 eq8816
    | (have j1 := eq8535 x y
       grind)
    | exact resolve eq8816 eq8535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8535 eq8816
  have eq9676 : (σ y) = (σ (k x x)) ∨ y = (k x x) := by grind
  clear eq9675
  have eq9681 : (k x x) = (τ (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq9676
       grind)
    | exact superpose eq9676 eq10
    | exact resolve eq10 eq9676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9676
  have eq9720 : y = (k x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq9681
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq9681
    | exact resolve eq9681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9681
  have eq9721 : y = (k x x) := by grind
  clear eq9720
  have eq9761 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2304 x
       have i₂ := eq9721
       grind)
    | exact superpose eq9721 eq2304
    | exact resolve eq2304 eq9721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304 eq9721
  have eq9769 : False := by grind
  exact eq9769

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq174 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq177 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq174 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq174 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq174 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq174 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1037 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq177
  have eq1053 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1037 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1435 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1053 (σ X1) (σ X0)
       grind)
    | exact superpose eq1053 eq15
    | exact resolve eq15 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1446 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1435 X0 X1
       have i₂ := eq1053 X1 X0
       grind)
    | exact superpose eq1053 eq1435
    | exact resolve eq1435 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053 eq1435
  have eq1456 : False := by grind
  exact eq1456

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pxx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
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
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X0) (σ X1)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq86
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq86
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq166 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq172 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 X1
       have i₂ := eq98 X1
       grind)
    | exact superpose eq98 eq171
    | (have j0 := eq171 X0 X1
       grind)
    | exact resolve eq171 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq197 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq172 x y
       grind)
    | exact superpose eq172 eq16
    | (have j1 := eq172 x y
       grind)
    | exact resolve eq16 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq546 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq197
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq197
    | (have j1 := eq59 y x
       grind)
    | exact resolve eq197 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq197
  have eq547 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq546
  have eq1512 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X1 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq166 X0 X1
       grind)
    | exact superpose eq166 eq109
    | exact resolve eq109 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq166
  have eq8857 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) (τ X0))) (M.op (σ (M.op (τ X0) (τ X0))) (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1512 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1512
    | exact resolve eq1512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq8971 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8857 X0 X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq8857
    | exact resolve eq8857 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq8857
  have eq9053 : y = (M.op (M.op x x) (M.op (M.op x x) (M.op x x))) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq8971 y y
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq8971
    | exact resolve eq8971 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq9142 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9053
       have i₂ := eq8971 x x
       grind)
    | exact superpose eq8971 eq9053
    | exact resolve eq9053 eq8971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9053
  have eq9540 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9142
       grind)
    | exact superpose eq9142 eq16
    | exact resolve eq16 eq9142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9142
  have eq9541 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq9540
       have r₂ := eq98 x
       grind)
    | exact resolve eq9540 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9540
  have eq9806 : (M.op y y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq9541
       grind)
    | exact superpose eq9541 eq10
    | exact resolve eq10 eq9541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9541
  have eq9866 : (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq9806
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq9806
    | exact resolve eq9806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9806
  have eq9945 : y = (M.op (M.op x x) (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq8971 y y
       have i₂ := eq9866
       grind)
    | exact superpose eq9866 eq8971
    | exact resolve eq8971 eq9866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9866
  have eq9947 : x = y := by
    first
    | (have i₁ := eq9945
       have i₂ := eq8971 x x
       grind)
    | exact superpose eq8971 eq9945
    | exact resolve eq9945 eq8971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8971 eq9945
  have eq10086 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9947
       grind)
    | exact superpose eq9947 eq16
    | exact resolve eq16 eq9947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9947
  have eq10087 : False := by grind
  exact eq10087

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_x_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq30 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq54 X0 X1 X2
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq158 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
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
  have eq176 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq158 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq294 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq61 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq61 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq406 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 (M.op X1 x)
       have i₂ := eq294 X1 x X0
       grind)
    | exact superpose eq294 eq9
    | exact resolve eq9 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq11398 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq176 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq11399 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11398 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11398
  have eq11447 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq11399 X0 (σ X1)
       grind)
    | exact superpose eq11399 eq23
    | (have j1 := eq11399 X0 (σ X1)
       grind)
    | exact resolve eq23 eq11399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq11448 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq11399 X0 (τ X1)
       grind)
    | exact superpose eq11399 eq19
    | (have j1 := eq11399 X0 (τ X1)
       grind)
    | exact resolve eq19 eq11399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq11552 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq11399 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11399 X0 (M.op X1 X1)
       grind)
    | exact superpose eq11399 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq11399 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11399 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq11399 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq11399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11399
  have eq12233 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq11447 X0 X1
       grind)
    | exact superpose eq11447 eq10
    | (have j1 := eq11447 X0 X1
       grind)
    | exact resolve eq10 eq11447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11447
  have eq12474 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11448 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11448
    | exact resolve eq11448 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11448
  have eq12718 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12474 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12474
    | (have j0 := eq12474 X0 X1
       grind)
    | exact resolve eq12474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12474
  have eq15201 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq12233 X0 X1
       grind)
    | exact superpose eq12233 eq11
    | (have j1 := eq12233 X0 X1
       grind)
    | exact resolve eq11 eq12233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12233
  have eq15210 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15201 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15201
    | (have j0 := eq15201 X0 X1
       grind)
    | exact resolve eq15201 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq15201
  have eq15281 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15210 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15210
    | (have j0 := eq15210 X1 (τ X0)
       grind)
    | exact resolve eq15210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15210
  have eq20105 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11552 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11552
  have eq20139 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq20105 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20105
  have eq20140 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq20139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20139
  have eq20152 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20140 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq20140
    | exact resolve eq20140 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20153 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20140 (τ X0)
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq20140
    | exact resolve eq20140 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq20164 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20153 X0
       have i₂ := eq20140 X0
       grind)
    | exact superpose eq20140 eq20153
    | exact resolve eq20153 eq20140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20153
  have eq20165 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20152 X0
       have i₂ := eq20140 X0
       grind)
    | exact superpose eq20140 eq20152
    | exact resolve eq20152 eq20140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20140 eq20152
  have eq20243 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq20164 X0
       grind)
    | exact superpose eq20164 eq9
    | exact resolve eq9 eq20164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20272 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq406 (τ X0) (τ X0) x
       have i₂ := eq20164 X0
       grind)
    | exact superpose eq20164 eq406
    | exact resolve eq406 eq20164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq20164
  have eq21075 : ∀ X0 X1 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15281 X1 (σ X0)
       have i₂ := eq20165 X0
       grind)
    | exact superpose eq20165 eq15281
    | (have j0 := eq15281 X1 (σ X0)
       grind)
    | exact resolve eq15281 eq20165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15281
  have eq21080 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq20165 X0
       grind)
    | exact superpose eq20165 eq9
    | exact resolve eq9 eq20165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21159 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21075 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq21075
    | (have j0 := eq21075 X0 X1
       grind)
    | exact resolve eq21075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21075
  have eq21707 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f21707_11 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
      intro X0 X1
      grind
    have f21707_13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f21707_20 : (τ X0) ≠ (M.op (M.op (τ X0) X1) (τ (M.op X0 (M.op X0 X0)))) := by grind
    have f21707_47 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (τ (M.op X0 (M.op X0 X0)))) := by
      intro X0 X1
      first
      | (have i₁ := f21707_11 (M.op x (M.op x x)) X1
         have i₂ := f21707_13 x (M.op x x) x
         grind)
      | exact superpose f21707_13 f21707_11
      | exact resolve f21707_11 f21707_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f21707_140 : (τ X0) ≠ (τ X0) := by
      first
      | (have i₁ := f21707_20
         have i₂ := f21707_47 X0 X1
         grind)
      | exact superpose f21707_47 f21707_20
      | (have r₁ := f21707_20
         have r₂ := f21707_47 X0 X1
         grind)
      | exact resolve f21707_20 f21707_47
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f21707_144 : False := by grind
    exact f21707_144
  clear eq20272
  have eq22428 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op (τ (σ X0)) X1) (τ (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq21707 (σ X0) X1
       have i₂ := eq20165 X0
       grind)
    | exact superpose eq20165 eq21707
    | exact resolve eq21707 eq20165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20165 eq21707
  have eq22531 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (τ (M.op (σ X0) (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22428 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22428
    | exact resolve eq22428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22428
  have eq23109 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (σ X0) (σ (M.op X0 X0))))) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20243 (M.op (σ X0) (σ (M.op X0 X0))) (M.op X0 X1)
       have i₂ := eq22531 X0 X1
       grind)
    | exact superpose eq22531 eq20243
    | exact resolve eq20243 eq22531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20243 eq22531
  have eq23194 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (τ (σ X0)) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23109 X0 X1
       have i₂ := eq21080 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq21080 eq23109
    | exact resolve eq23109 eq21080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21080 eq23109
  have eq23214 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23194 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23194
    | exact resolve eq23194 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23194
  have eq23228 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq23214 X0 x
       have i₂ := eq60 X0 X0 x
       grind)
    | exact superpose eq60 eq23214
    | exact resolve eq23214 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq23214
  have eq23777 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ (M.op X0 X0)))
       have i₂ := eq23228 X0
       grind)
    | exact superpose eq23228 eq11
    | exact resolve eq11 eq23228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23228
  have eq25724 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21159 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21159
    | (have j0 := eq21159 X1 (σ X0)
       grind)
    | exact resolve eq21159 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21159
  have eq26026 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25724 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq25724
    | (have j0 := eq25724 X0 X1
       grind)
    | exact resolve eq25724 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25724
  have eq27417 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26026 y x
       grind)
    | exact superpose eq26026 eq16
    | (have j1 := eq26026 y x
       grind)
    | exact resolve eq16 eq26026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26026
  have eq27754 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq27417
       have i₂ := eq12718 y x
       grind)
    | exact superpose eq12718 eq27417
    | (have j1 := eq12718 y x
       grind)
    | (have r₁ := eq27417
       have r₂ := eq12718 y x
       grind)
    | exact resolve eq27417 eq12718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12718 eq27417
  have eq27759 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq27754
  have eq27760 : y = (M.op x x) := by grind
  clear eq27759
  have eq27813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23777 x
       have i₂ := eq27760
       grind)
    | exact superpose eq27760 eq23777
    | exact resolve eq23777 eq27760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23777 eq27760
  have eq30848 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27813
       grind)
    | exact superpose eq27813 eq16
    | (have r₁ := eq16
       have r₂ := eq27813
       grind)
    | exact resolve eq16 eq27813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27813
  have eq30920 : False := by grind
  exact eq30920

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_y_pyx_Equation1469 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
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
  have eq53 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x (M.op x y))) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq92 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq92
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq218 : ∀ X1 : G, (M.op x y) = (M.op x (M.op X1 (M.op X1 (M.op x y)))) := by
    intro X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X1 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq55 X0 X1 X2
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq218 eq55
    | exact resolve eq55 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq561 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq221 eq55
    | exact resolve eq55 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq221
  have eq4639 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 x))) := by
    intro X0
    first
    | exact superpose eq53 eq555
    | exact resolve eq555 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq4643 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq54 eq555
    | exact resolve eq555 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq555
  have eq13258 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq13258
    | exact resolve eq13258 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13258
  have eq13270 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq13259
       have r₂ := eq28
       grind)
    | exact resolve eq13259 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13259
  have eq13274 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq13270
    | exact resolve eq13270 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13270
  have eq13289 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13274 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13274
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13274
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13274
       grind)
    | exact resolve eq12 eq13274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13274
  have eq13311 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq13289
  have eq13315 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq13311
       have r₂ := eq27
       grind)
    | exact resolve eq13311 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13311
  have eq13572 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13315 eq104
    | exact resolve eq104 eq13315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq13573 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13315 eq107
    | exact resolve eq107 eq13315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq13315
  have eq13582 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13573
  have eq13592 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq29 eq13572
    | exact resolve eq13572 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13572
  have eq13604 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq13582
       grind)
    | exact superpose eq13582 eq56
    | exact resolve eq56 eq13582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq13608 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4639 y
       have i₂ := eq13582
       grind)
    | exact superpose eq13582 eq4639
    | exact resolve eq4639 eq13582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639 eq13582
  have eq13640 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq559 eq13608
    | exact resolve eq13608 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq13608
  have eq14087 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq13592
       grind)
    | exact superpose eq13592 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13592
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13592
       grind)
    | exact resolve eq12 eq13592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13592
  have eq14109 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq14087
  have eq14112 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14109
       have r₂ := eq19
       grind)
    | exact resolve eq14109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14109
  have eq14118 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq14112
       grind)
    | exact superpose eq14112 eq92
    | exact resolve eq92 eq14112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq14112
  have eq14135 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14118
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14118
    | exact resolve eq14118 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14118
  have eq14168 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14135 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq14135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14135
  have eq14169 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14168
  have eq14173 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq14169
    | exact resolve eq14169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14169
  have eq14184 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq14173
    | exact resolve eq14173 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq15315 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13640 eq13604
    | exact resolve eq13604 eq13640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13604 eq13640
  have eq15349 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq15315
  have eq15354 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq15349 eq30
    | exact resolve eq30 eq15349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15349
  have eq15471 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq15354
    | exact resolve eq15354 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15354
  have eq15472 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq15471
  have eq15515 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq15472 eq29
    | exact resolve eq29 eq15472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq15597 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ (M.op x y))))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq15472 eq4643
    | exact resolve eq4643 eq15472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643
  have eq15622 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15472 eq14184
    | exact resolve eq14184 eq15472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14184 eq15472
  have eq15623 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq15622
  have eq15642 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq15623
       have r₂ := eq28
       grind)
    | exact resolve eq15623 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15623
  have eq15693 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq15515
    | exact resolve eq15515 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15515
  have eq18565 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15642 eq57
    | exact resolve eq57 eq15642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq21013 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15642 eq15597
    | exact resolve eq15597 eq15642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15597 eq15642
  have eq21066 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq21013
  have eq21069 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq561 eq21066
    | exact resolve eq21066 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq21066
  have eq46576 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21069 eq18565
    | exact resolve eq18565 eq21069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18565 eq21069
  have eq46648 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq46576
  have eq46659 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq46648 eq30
    | exact resolve eq30 eq46648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq46648
  have eq46855 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq46659
    | exact resolve eq46659 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq46659
  have eq46981 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq46855 eq15693
    | exact resolve eq15693 eq46855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15693 eq46855
  have eq47082 : x = y := by grind
  clear eq46981
  have eq47190 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq47082
       grind)
    | exact superpose eq47082 eq19
    | exact resolve eq19 eq47082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq47191 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq47082
       grind)
    | exact superpose eq47082 eq25
    | exact resolve eq25 eq47082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq47082
  have eq47307 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq47191
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq47191
    | exact resolve eq47191 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq47191
  have eq47324 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq47307 eq27
    | exact resolve eq27 eq47307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq47307
  have eq47665 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq47324 eq71
    | exact resolve eq71 eq47324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq47324
  have eq47762 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq47665
       have i₂ := eq47190
       grind)
    | exact superpose eq47190 eq47665
    | exact resolve eq47665 eq47190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47190 eq47665
  have eq47777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47762 eq15
    | exact resolve eq15 eq47762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47762
  have eq47823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq47777
    | exact resolve eq47777 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq47777
  have eq47832 : False := by grind
  exact eq47832
