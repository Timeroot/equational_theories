import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq88 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq91 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | (have j0 := eq88 X0
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq168 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq92 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq92
    | (have j0 := eq92 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq92 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq92
    | (have j0 := eq92 (σ X0) (σ X1)
       grind)
    | exact resolve eq92 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq92 X1 X0
       grind)
    | exact superpose eq92 eq10
    | (have j1 := eq92 X1 X0
       grind)
    | exact resolve eq10 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq1651 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq98 (τ X0) X0
       grind)
    | exact superpose eq98 eq91
    | (have j0 := eq91 X0
       have j1 := eq98 (τ X0) X0
       grind)
    | exact resolve eq91 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq98
  have eq1658 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq1660 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1658 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1658
    | (have j0 := eq1658 X0
       grind)
    | exact resolve eq1658 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq1680 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = X1 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq1660 X0
       grind)
    | exact superpose eq1660 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq1660 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq1660 X0
       grind)
    | exact resolve eq12 eq1660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1717 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1680 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq1743 : ∀ X0 X1 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (k X1 (τ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (τ X0) X0 (τ X0)
       have i₂ := eq1717 (τ X0) X1
       grind)
    | exact superpose eq1717 eq28
    | (have j1 := eq1717 (τ X0) X1
       grind)
    | exact resolve eq28 eq1717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1748 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq1717 (σ X0) X1
       grind)
    | exact superpose eq1717 eq23
    | (have j1 := eq1717 (σ X0) X1
       grind)
    | exact resolve eq23 eq1717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1764 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k (τ (σ X0)) X0) X0) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1748 X0 X1
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq1748
    | (have j0 := eq1748 X0 X1
       grind)
    | exact resolve eq1748 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1748
  have eq1767 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (k X1 (τ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1743 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1743
    | (have j0 := eq1743 X0 X1
       grind)
    | exact resolve eq1743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1780 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1764 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1764
    | (have j0 := eq1764 X0 X1
       grind)
    | exact resolve eq1764 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq1786 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1780 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1780
    | (have j0 := eq1780 X0 X1
       grind)
    | exact resolve eq1780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq1798 : ∀ X0 X1 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq1786 X0 X1
       grind)
    | exact superpose eq1786 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq1786 X0 X1
       grind)
    | exact resolve eq14 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1807 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1786 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1817 : ∀ X0 X1 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1798 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1798 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1798 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq2193 : ∀ X0 X1 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (k X1 (τ (τ (τ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (τ X0) X0 (τ X0)
       have i₂ := eq1767 (τ X0) X1
       grind)
    | exact superpose eq1767 eq28
    | (have j1 := eq1767 (τ X0) X1
       grind)
    | exact resolve eq28 eq1767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1767
  have eq2217 : ∀ X0 X1 : G, (k X1 (τ (τ (τ X0)))) = X1 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2193 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2193
    | (have j0 := eq2193 X0 X1
       grind)
    | exact resolve eq2193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2290 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1807 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq1807
    | exact resolve eq1807 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq2292 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2290 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq2290
    | (have j0 := eq2290 X0
       grind)
    | exact resolve eq2290 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq3882 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ (k X0 X0))) ∨ (τ (τ (k X0 X0))) = (τ (k (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2292 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq2292
    | exact resolve eq2292 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292
  have eq3894 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ (k X0 X0))) ∨ (τ (τ (k X0 X0))) = (τ (τ (k (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq3882 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq3882
    | (have j0 := eq3882 X0
       grind)
    | exact resolve eq3882 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3882
  have eq4530 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (k X0 X0)
       have i₂ := eq1817 X0 X1
       grind)
    | exact superpose eq1817 eq66
    | (have j1 := eq1817 X0 X1
       grind)
    | exact resolve eq66 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq4644 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4530 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq4530 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq4530 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4530
  have eq4671 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4644 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4644
    | (have j0 := eq4644 (σ X0) X1
       grind)
    | exact resolve eq4644 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4744 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4671 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq4671
    | (have j0 := eq4671 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq4671 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq4782 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4744 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4744
  have eq11749 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq170 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq11750 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq11749 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11749
  have eq11952 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq168 x y
       grind)
    | exact superpose eq168 eq16
    | (have j1 := eq168 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq168 x y
       grind)
    | exact resolve eq16 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq12022 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq11952
  have eq12739 : ∀ X0 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq11750 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq11750
    | (have j0 := eq11750 (τ X0)
       grind)
    | exact resolve eq11750 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11750
  have eq12760 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq12739 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12739
    | (have j0 := eq12739 X0
       grind)
    | exact resolve eq12739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12739
  have eq12774 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12760 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12760
    | (have j0 := eq12760 X0
       grind)
    | exact resolve eq12760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12760
  have eq12803 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12774 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq12774
    | (have j0 := eq12774 (τ X0)
       grind)
    | exact resolve eq12774 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq12824 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12803 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12803
    | (have j0 := eq12803 X0
       grind)
    | exact resolve eq12803 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12803
  have eq12838 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12824 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12824
    | (have j0 := eq12824 X0
       grind)
    | exact resolve eq12824 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12824
  have eq12858 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12838 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq12838
    | (have j0 := eq12838 (τ X0)
       grind)
    | exact resolve eq12838 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12838
  have eq16306 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66 (σ X0) (σ X0)
       have i₂ := eq4782 X0 X1
       grind)
    | exact superpose eq4782 eq66
    | (have j1 := eq4782 X0 X1
       grind)
    | exact resolve eq66 eq4782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4782
  have eq18110 : ∀ X0 : G, (τ (τ (τ (τ (τ X0))))) ≠ (τ (τ (τ (τ (τ X0))))) ∨ (τ (τ (τ (τ (τ X0))))) = (τ (τ (k (τ (τ (τ X0))) (τ (τ (τ X0)))))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3894 (τ (τ (τ X0)))
       have i₂ := eq2217 X0 (τ (τ (τ X0)))
       grind)
    | exact superpose eq2217 eq3894
    | (have j1 := eq2217 X0 x
       grind)
    | exact resolve eq3894 eq2217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq18141 : ∀ X0 : G, (τ (τ (τ (τ (τ X0))))) = (τ (τ (k (τ (τ (τ X0))) (τ (τ (τ X0)))))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq18110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18110
  have eq18174 : ∀ X0 : G, (τ (τ (τ (τ (τ X0))))) = (τ (τ (τ (k (τ (τ X0)) (τ (τ X0)))))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18141 X0
       have i₂ := eq32 (τ (τ X0)) (τ (τ X0))
       grind)
    | exact superpose eq32 eq18141
    | (have j0 := eq18141 X0
       grind)
    | exact resolve eq18141 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18141
  have eq18208 : ∀ X0 : G, (τ (τ (τ (τ (τ X0))))) = (τ (τ (τ (τ (k (τ X0) (τ X0)))))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18174 X0
       have i₂ := eq32 (τ X0) (τ X0)
       grind)
    | exact superpose eq32 eq18174
    | (have j0 := eq18174 X0
       grind)
    | exact resolve eq18174 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18174
  have eq18237 : ∀ X0 : G, (τ (τ (τ (τ (τ X0))))) = (τ (τ (τ (τ (τ (k X0 X0)))))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18208 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq18208
    | (have j0 := eq18208 X0
       grind)
    | exact resolve eq18208 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq18208
  have eq18649 : ∀ X0 : G, (σ (τ (τ (τ (τ (τ X0)))))) = (τ (τ (τ (τ (k X0 X0))))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (τ (τ (τ (τ (k X0 X0)))))
       have i₂ := eq18237 X0
       grind)
    | exact superpose eq18237 eq11
    | (have j1 := eq18237 X0
       grind)
    | exact resolve eq11 eq18237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18237
  have eq18717 : ∀ X0 : G, (τ (τ (τ (τ X0)))) = (τ (τ (τ (τ (k X0 X0))))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18649 X0
       have i₂ := eq11 (τ (τ (τ (τ X0))))
       grind)
    | exact superpose eq11 eq18649
    | (have j0 := eq18649 X0
       grind)
    | exact resolve eq18649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18649
  have eq18944 : ∀ X0 : G, (σ (τ (τ (τ (τ X0))))) = (τ (τ (τ (k X0 X0)))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (τ (τ (τ (k X0 X0))))
       have i₂ := eq18717 X0
       grind)
    | exact superpose eq18717 eq11
    | (have j1 := eq18717 X0
       grind)
    | exact resolve eq11 eq18717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18717
  have eq19012 : ∀ X0 : G, (τ (τ (τ X0))) = (τ (τ (τ (k X0 X0)))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18944 X0
       have i₂ := eq11 (τ (τ (τ X0)))
       grind)
    | exact superpose eq11 eq18944
    | (have j0 := eq18944 X0
       grind)
    | exact resolve eq18944 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18944
  have eq19182 : ∀ X0 : G, (σ (τ (τ (τ X0)))) = (τ (τ (k X0 X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (τ (τ (k X0 X0)))
       have i₂ := eq19012 X0
       grind)
    | exact superpose eq19012 eq11
    | (have j1 := eq19012 X0
       grind)
    | exact resolve eq11 eq19012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19012
  have eq19247 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (k X0 X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19182 X0
       have i₂ := eq11 (τ (τ X0))
       grind)
    | exact superpose eq11 eq19182
    | (have j0 := eq19182 X0
       grind)
    | exact resolve eq19182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19182
  have eq19353 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (τ (τ X0)) = (τ (τ (k (k X0 X0) X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3894 X0
       have i₂ := eq19247 X0
       grind)
    | exact superpose eq19247 eq3894
    | (have j1 := eq19247 X0
       grind)
    | (have r₁ := eq3894 X0
       have r₂ := eq19247 X0
       grind)
    | exact resolve eq3894 eq19247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3894 eq19247
  have eq19414 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (k (k X0 X0) X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19353
  have eq20021 : ∀ X0 : G, (τ (k (k X0 X0) X0)) = (σ (τ (τ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (τ (k (k X0 X0) X0))
       have i₂ := eq19414 X0
       grind)
    | exact superpose eq19414 eq11
    | (have j1 := eq19414 X0
       grind)
    | exact resolve eq11 eq19414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19414
  have eq20082 : ∀ X0 : G, (τ X0) = (τ (k (k X0 X0) X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20021 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq20021
    | (have j0 := eq20021 X0
       grind)
    | exact resolve eq20021 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20021
  have eq20182 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 X0) X0) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k (k X0 X0) X0)
       have i₂ := eq20082 X0
       grind)
    | exact superpose eq20082 eq11
    | (have j1 := eq20082 X0
       grind)
    | exact resolve eq11 eq20082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20082
  have eq20240 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20182 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20182
    | (have j0 := eq20182 X0
       grind)
    | exact resolve eq20182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20182
  have eq20241 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq20240 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20240
  have eq20322 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq20241 X0
       grind)
    | exact superpose eq20241 eq14
    | (have j0 := eq14 X0 X0
       grind)
    | exact resolve eq14 eq20241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20241
  have eq20374 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq4644 eq20322
    | (have j0 := eq20322 X0
       have j1 := eq4644 X0 x
       grind)
    | exact resolve eq20322 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644 eq20322
  have eq20375 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq20374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20374
  have eq51442 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq184 x x
       have i₂ := eq12022
       grind)
    | exact superpose eq12022 eq184
    | (have j0 := eq184 x x
       grind)
    | exact resolve eq184 eq12022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq51596 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq12022
  have eq51600 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq51442
  have eq51664 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq51600
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq51600
    | exact resolve eq51600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51600
  have eq51716 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20375 eq51664
    | (have j1 := eq20375 (σ x)
       grind)
    | exact resolve eq51664 eq20375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20375 eq51664
  have eq51717 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq51716
  have eq51767 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq51717
       have r₂ := eq51596
       grind)
    | exact resolve eq51717 eq51596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51596 eq51717
  have eq51827 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq51767
       grind)
    | exact superpose eq51767 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq51767
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq51767
       grind)
    | exact resolve eq12 eq51767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51767
  have eq51965 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq51827 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51827
  have eq52136 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12858 (σ x)
       have i₂ := eq51965 (σ x)
       grind)
    | exact superpose eq51965 eq12858
    | (have j0 := eq12858 (σ x)
       grind)
    | exact resolve eq12858 eq51965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52179 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ x)
       have i₂ := eq51965 (σ X0)
       grind)
    | exact superpose eq51965 eq29
    | exact resolve eq29 eq51965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq51965
  have eq52249 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq52136
  have eq52313 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52179 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52179
    | exact resolve eq52179 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52179
  have eq52340 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52249
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52249
    | exact resolve eq52249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52249
  have eq52341 : x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq52340
  have eq52397 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52313 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq52313
    | exact resolve eq52313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52313
  have eq52434 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq52341
  have eq52471 : ∀ X0 : G, y = (M.op x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq52397 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq52397 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq52397 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52397
  have eq52538 : ∀ X0 : G, x ≠ y ∨ (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq52434
       grind)
    | exact superpose eq52434 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq52434
       grind)
    | exact resolve eq12 eq52434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52578 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16306 x x
       have i₂ := eq52434
       grind)
    | exact superpose eq52434 eq16306
    | (have j0 := eq16306 x X0
       grind)
    | exact resolve eq16306 eq52434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16306
  have eq52594 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66 x x
       have i₂ := eq52434
       grind)
    | exact superpose eq52434 eq66
    | exact resolve eq66 eq52434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq52687 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq52434
  have eq52698 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq52578 X0
       grind)
    | (have r₁ := eq52578 X0
       have r₂ := eq52687
       grind)
    | exact resolve eq52578 eq52687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52578 eq52687
  have eq52738 : ∀ X0 : G, x ≠ y ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq52538 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq52538 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq52538 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52538
  have eq69227 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq52698 X0
       grind)
    | exact superpose eq52698 eq16
    | (have j1 := eq52698 X0
       grind)
    | exact resolve eq16 eq52698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52698
  have eq69383 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq52594 eq69227
    | (have j0 := eq69227 X0
       grind)
    | exact resolve eq69227 eq52594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52594 eq69227
  have eq69384 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq69383 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69383
  have eq69462 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12858 (σ x)
       have i₂ := eq69384 (σ x)
       grind)
    | exact superpose eq69384 eq12858
    | (have j0 := eq12858 (σ x)
       grind)
    | exact resolve eq12858 eq69384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12858 eq69384
  have eq69577 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by grind
  clear eq69462
  have eq69671 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69577
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq69577
    | exact resolve eq69577 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69577
  have eq69672 : x = (M.op x x) := by grind
  clear eq69671
  have eq69881 : ∀ X0 : G, x = y ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq52471 X0
       have i₂ := eq69672
       grind)
    | exact superpose eq69672 eq52471
    | (have j0 := eq52471 X0
       grind)
    | exact resolve eq52471 eq69672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52471
  have eq69925 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 x x X0
       have i₂ := eq69672
       grind)
    | exact superpose eq69672 eq68
    | exact resolve eq68 eq69672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69672
  have eq70104 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq69925 X0
       have i₂ := eq64 x X0
       grind)
    | exact superpose eq64 eq69925
    | exact resolve eq69925 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69925
  have eq70137 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq69881 X0
       have j1 := eq52738 X0
       grind)
    | (have r₁ := eq69881 X0
       have r₂ := eq52738 X0
       grind)
    | exact resolve eq69881 eq52738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52738 eq69881
  have eq70189 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12774 x
       have i₂ := eq70137 x
       grind)
    | exact superpose eq70137 eq12774
    | (have j0 := eq12774 x
       grind)
    | exact resolve eq12774 eq70137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12774 eq70137
  have eq70289 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq70189
  have eq71122 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70104 y
       grind)
    | exact superpose eq70104 eq16
    | exact resolve eq16 eq70104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70104
  have eq74723 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 (σ x) (σ x) X0
       have i₂ := eq70289
       grind)
    | exact superpose eq70289 eq68
    | exact resolve eq68 eq70289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq70289
  have eq74898 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq74723 X0
       have i₂ := eq64 (σ x) X0
       grind)
    | exact superpose eq64 eq74723
    | exact resolve eq74723 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq74723
  have eq74914 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq71122
       have i₂ := eq74898 (σ y)
       grind)
    | exact superpose eq74898 eq71122
    | (have r₁ := eq71122
       have r₂ := eq74898 (σ y)
       grind)
    | exact resolve eq71122 eq74898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71122 eq74898
  have eq75103 : False := by grind
  exact eq75103

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq105 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq111 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq105 X0 X1
       grind)
    | exact superpose eq105 eq9
    | exact resolve eq9 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq825 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq359
    | (have j0 := eq359 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq359 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq23734 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq825 x y
       grind)
    | exact superpose eq825 eq16
    | (have j1 := eq825 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq825 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq825 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq825 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq23823 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq23734
  have eq44954 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq23823
       grind)
    | exact superpose eq23823 eq16
    | exact resolve eq16 eq23823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44968 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq23823
       grind)
    | exact superpose eq23823 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq23823
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq23823
       grind)
    | exact resolve eq13 eq23823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23823
  have eq45031 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq44968
  have eq45032 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq45031
  have eq45083 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq45032
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq45032
    | exact resolve eq45032 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45032
  have eq45099 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14 eq45083
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq45083 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45083
  have eq45103 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq45099
       have r₂ := eq44954
       grind)
    | exact resolve eq45099 eq44954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44954 eq45099
  have eq45115 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq111 x y X0
       have i₂ := eq45103
       grind)
    | exact superpose eq45103 eq111
    | exact resolve eq111 eq45103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq45219 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq45115 X0
       have i₂ := eq105 x X0
       grind)
    | exact superpose eq105 eq45115
    | exact resolve eq45115 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq45115
  have eq45907 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq45219 X0
       grind)
    | exact superpose eq45219 eq10
    | (have j1 := eq45219 X0
       grind)
    | exact resolve eq10 eq45219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45219
  have eq46118 : ∀ X0 : G, x = y ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq45907 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq45907
    | (have j0 := eq45907 X0
       grind)
    | exact resolve eq45907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45907
  have eq46119 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq46118 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46118
  have eq46123 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq45103
       have i₂ := eq46119 y
       grind)
    | exact superpose eq46119 eq45103
    | exact resolve eq45103 eq46119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45103 eq46119
  have eq46281 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq46123
  have eq46791 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq46281
       grind)
    | exact superpose eq46281 eq10
    | exact resolve eq10 eq46281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46281
  have eq46998 : x = y ∨ x = y := by
    first
    | (have i₁ := eq46791
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq46791
    | exact resolve eq46791 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46791
  have eq46999 : x = y := by grind
  clear eq46998
  have eq47421 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46999
       grind)
    | exact superpose eq46999 eq16
    | exact resolve eq16 eq46999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46999
  have eq47422 : False := by grind
  exact eq47422

/-- `Equation3201`: `x = (((y ◇ z) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_pyx_pxy_Equation3201 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3201 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3201.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq76 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq77 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82
    | exact resolve eq82 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq114 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | (have j0 := eq114 y x
       grind)
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq114
    | (have j0 := eq114 (σ y) (σ x)
       grind)
    | exact resolve eq114 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X1) X2) ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq114
    | (have r₁ := eq114 (M.op (M.op (M.op X1 X2) X1) X2) (M.op (M.op (M.op X1 X2) X1) X2)
       have r₂ := eq14 (M.op (M.op (M.op X1 X2) X1) X2) X1 X2
       grind)
    | exact resolve eq114 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op (M.op (M.op x y) x) y) ≠ X0 ∨ (k X0 (M.op (M.op (M.op x y) x) y)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq114
    | (have r₁ := eq114 (M.op (M.op (M.op x y) x) y) (M.op (M.op (M.op x y) x) y)
       have r₂ := eq50 (M.op (M.op (M.op x y) x) y)
       grind)
    | exact resolve eq114 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq405 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq236
    | exact resolve eq236 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq621 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (k (M.op (M.op (M.op X0 X1) X0) X1) (M.op (M.op (M.op X0 X1) X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq125 (M.op (M.op (M.op X0 X1) X0) X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq695 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq700 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq695 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq695 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq695 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq695 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq710 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq700 X0 X1
       have j1 := eq114 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq700 X0 X1
       have r₂ := eq114 (σ X0) (σ X1)
       grind)
    | exact resolve eq700 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq717 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq710
    | (have j0 := eq710 X0 X1
       grind)
    | exact resolve eq710 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq3014 : (M.op (M.op (M.op x y) x) y) = (k (M.op (M.op (M.op x y) x) y) (M.op (M.op (M.op x y) x) y)) := by
    first
    | (have j0 := eq213 (M.op (M.op (M.op x y) x) y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq3673 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq717 (τ X1) (τ X0)
       have i₂ := eq405 X0 X1
       grind)
    | exact superpose eq405 eq717
    | exact resolve eq717 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq3845 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3673 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq3673
    | (have j0 := eq3673 X0 X1
       grind)
    | exact resolve eq3673 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673
  have eq3931 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3845 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3845
    | (have j0 := eq3845 X0 X1
       grind)
    | exact resolve eq3845 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845
  have eq4013 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3931 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3931
    | (have j0 := eq3931 X0 X1
       grind)
    | exact resolve eq3931 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3931
  have eq4021 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4013 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq4013
    | (have j0 := eq4013 X0 X1
       grind)
    | exact resolve eq4013 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4013
  have eq4028 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4021 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq4021
    | (have j0 := eq4021 X0 X1
       grind)
    | exact resolve eq4021 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021
  have eq4256 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq76 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq76
    | (have j0 := eq76 x
       grind)
    | exact resolve eq76 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq4267 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4256
  have eq4272 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4267
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4267
    | exact resolve eq4267 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4267
  have eq4289 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4272
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq4272 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4272
  have eq4297 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4289 eq49
    | exact resolve eq49 eq4289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq4289
  have eq4442 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq77
    | (have j0 := eq77 y
       grind)
    | exact resolve eq77 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4444 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq77 eq13
    | (have j0 := eq13 (σ y) (σ X0)
       have j1 := eq77 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ y)
       have r₂ := eq77 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ X0)
       have r₂ := eq77 X0
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq4452 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4442
  have eq4454 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4444 X0
       have j1 := eq13 (σ y) (σ X0)
       grind)
    | (have r₁ := eq4444 X0
       have r₂ := eq13 (σ X0) (σ y)
       grind)
    | (have r₁ := eq4444 X0
       have r₂ := eq13 (σ y) (σ X0)
       grind)
    | exact resolve eq4444 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4444
  have eq4456 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4452
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq4452
    | exact resolve eq4452 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq4452
  have eq4479 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4454 X0
       have j1 := eq114 (σ y) (σ X0)
       grind)
    | (have r₁ := eq4454 X0
       have r₂ := eq114 (σ y) (σ X0)
       grind)
    | exact resolve eq4454 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4480 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4456
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4456 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4456
  have eq4491 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq4479
    | (have j0 := eq4479 X0
       grind)
    | exact resolve eq4479 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4479
  have eq4504 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4480 eq106
    | exact resolve eq106 eq4480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq4480
  have eq15053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15053
    | exact resolve eq15053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15053
  have eq15072 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq15061
       have r₂ := eq27
       grind)
    | exact resolve eq15061 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15061
  have eq15074 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15072
    | exact resolve eq15072 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15072
  have eq15080 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15074 eq114
    | (have r₁ := eq114 (σ x) (σ y)
       have r₂ := eq15074
       grind)
    | (have r₁ := eq114 (σ y) (σ x)
       have r₂ := eq15074
       grind)
    | (have r₁ := eq114 y x
       have r₂ := eq15074
       grind)
    | exact resolve eq114 eq15074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15074
  have eq15089 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq15080
  have eq15490 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15089 eq57
    | exact resolve eq57 eq15089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq15491 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15089 eq93
    | exact resolve eq93 eq15089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15089
  have eq15509 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15491
  have eq15517 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq15490
    | exact resolve eq15490 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15490
  have eq15521 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15509
       grind)
    | exact superpose eq15509 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15509
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15509
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15509
       grind)
    | exact resolve eq13 eq15509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15525 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq114 x y
       have i₂ := eq15509
       grind)
    | exact superpose eq15509 eq114
    | (have r₁ := eq114 x y
       have r₂ := eq15509
       grind)
    | (have r₁ := eq114 y x
       have r₂ := eq15509
       grind)
    | (have r₁ := eq114 (σ y) (σ x)
       have r₂ := eq15509
       grind)
    | exact resolve eq114 eq15509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq15509
  have eq15534 : y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15525
  have eq15535 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15521
  have eq15537 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15535
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15535
    | exact resolve eq15535 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15535
  have eq15538 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15537
       have r₂ := eq123
       grind)
    | exact resolve eq15537 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15537
  have eq15542 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15538
       grind)
    | exact superpose eq15538 eq72
    | exact resolve eq72 eq15538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq15538
  have eq15571 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15542
    | exact resolve eq15542 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15542
  have eq15630 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15571 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq15571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15638 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15630
    | exact resolve eq15630 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15630
  have eq15639 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15638
  have eq15653 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq15534
       grind)
    | exact superpose eq15534 eq44
    | exact resolve eq44 eq15534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15534
  have eq15680 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15653
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15653
    | exact resolve eq15653 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15653
  have eq15740 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15680 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq15680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15680
  have eq15750 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15740
    | exact resolve eq15740 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15740
  have eq15761 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15750
    | exact resolve eq15750 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15750
  have eq15762 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15761
  have eq17051 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15517
       grind)
    | exact superpose eq15517 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15517
  have eq17060 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17051
  have eq17068 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17060
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17060
    | exact resolve eq17060 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17060
  have eq17083 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17068
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17068
    | exact resolve eq17068 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17068
  have eq17084 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17083
  have eq17107 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq17084
       grind)
    | exact superpose eq17084 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17084
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17084
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17084
       grind)
    | exact resolve eq13 eq17084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17084
  have eq17121 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17107
  have eq17123 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17121
    | exact resolve eq17121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17121
  have eq17124 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17123
       have r₂ := eq123
       grind)
    | exact resolve eq17123 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17123
  have eq17140 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq717 y x
       have i₂ := eq17124
       grind)
    | exact superpose eq17124 eq717
    | exact resolve eq717 eq17124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17124
  have eq17144 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17140
    | exact resolve eq17140 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17140
  have eq17159 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17144
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17144
    | exact resolve eq17144 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17144
  have eq17167 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17159
    | exact resolve eq17159 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17159
  have eq17173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17167
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17167
    | exact resolve eq17167 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17167
  have eq17179 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17173
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17173
    | exact resolve eq17173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17173
  have eq17186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17179
    | exact resolve eq17179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17179
  have eq17194 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17186
       have r₂ := eq27
       grind)
    | exact resolve eq17186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17186
  have eq17852 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15639 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15639
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15639
       grind)
    | exact resolve eq13 eq15639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15639
  have eq17867 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq17852
  have eq17868 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq17867
    | exact resolve eq17867 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17867
  have eq17869 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq17868
       have r₂ := eq124
       grind)
    | exact resolve eq17868 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17868
  have eq17886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq17869 eq15571
    | exact resolve eq15571 eq17869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15571 eq17869
  have eq17908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq17886
  have eq17922 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq17908
       have r₂ := eq27
       grind)
    | exact resolve eq17908 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17908
  have eq18999 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15762 eq17922
    | exact resolve eq17922 eq15762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15762
  have eq19015 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq18999
  have eq19024 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19015 eq51
    | exact resolve eq51 eq19015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19015
  have eq55060 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19024 eq14
    | exact resolve eq14 eq19024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19024
  have eq55153 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55060 eq4297
    | exact resolve eq4297 eq55060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4297 eq55060
  have eq55227 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq55153
    | exact resolve eq55153 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55153
  have eq55634 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4028 x x
       have i₂ := eq55227
       grind)
    | exact superpose eq55227 eq4028
    | (have r₁ := eq4028 x x
       have r₂ := eq55227
       grind)
    | exact resolve eq4028 eq55227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55227
  have eq55635 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq55634
  have eq55682 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq55635
       grind)
    | exact superpose eq55635 eq14
    | exact resolve eq14 eq55635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55635
  have eq70134 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq55682 x
       grind)
    | exact superpose eq55682 eq14
    | exact resolve eq14 eq55682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55682
  have eq70225 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq70134 y
       grind)
    | exact superpose eq70134 eq18
    | (have j1 := eq70134 y
       grind)
    | exact resolve eq18 eq70134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70134
  have eq70295 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq70225
       have r₂ := eq17194
       grind)
    | exact resolve eq70225 eq17194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17194 eq70225
  have eq70310 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70295 eq27
    | exact resolve eq27 eq70295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70312 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70295 eq64
    | (have r₁ := eq64
       have r₂ := eq70295
       grind)
    | exact resolve eq64 eq70295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq70313 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70295 eq124
    | (have r₁ := eq124
       have r₂ := eq70295
       grind)
    | exact resolve eq124 eq70295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq70295
  have eq70329 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq70313
  have eq70330 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq70312
  have eq70731 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70329 eq99
    | exact resolve eq99 eq70329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq70329
  have eq70899 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq70731
    | exact resolve eq70731 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq70731
  have eq71372 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq70899
       grind)
    | exact superpose eq70899 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq70899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71379 : x ≠ y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4028 y x
       have i₂ := eq70899
       grind)
    | exact superpose eq70899 eq4028
    | exact resolve eq4028 eq70899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71421 : x = (M.op x y) ∨ x ≠ y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71379
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq71379
    | exact resolve eq71379 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71379
  have eq71422 : x ≠ y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq71421
  have eq71429 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71372
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq71372
    | exact resolve eq71372 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71372
  have eq71430 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq71429
  have eq71872 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70330 eq93
    | exact resolve eq93 eq70330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq70330
  have eq71918 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq71872
  have eq89191 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq71430
       grind)
    | exact superpose eq71430 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq71430
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq71430
       grind)
    | exact resolve eq13 eq71430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71430
  have eq89206 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq89191
  have eq89208 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq89206
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89206
    | exact resolve eq89206 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89206
  have eq89209 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq89208
       have r₂ := eq123
       grind)
    | exact resolve eq89208 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89208
  have eq89261 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70899
       have i₂ := eq89209
       grind)
    | exact superpose eq89209 eq70899
    | exact resolve eq70899 eq89209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70899 eq89209
  have eq89272 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq89261
  have eq89379 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq89272
       grind)
    | exact superpose eq89272 eq14
    | exact resolve eq14 eq89272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89272
  have eq89417 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq89379 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89379
    | (have j0 := eq89379 X0
       grind)
    | exact resolve eq89379 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq89379
  have eq89566 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq89417 eq50
    | exact resolve eq50 eq89417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89573 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq89417 eq3014
    | exact resolve eq3014 eq89417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014 eq89417
  have eq89787 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq717 y y
       have i₂ := eq89573
       grind)
    | exact superpose eq89573 eq717
    | exact resolve eq717 eq89573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89573
  have eq89792 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq89787
  have eq89804 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89792
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq89792
    | exact resolve eq89792 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89792
  have eq89848 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq89804 eq14
    | exact resolve eq14 eq89804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89804
  have eq90831 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq89848 eq14
    | exact resolve eq14 eq89848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89848
  have eq91323 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq90831 eq71918
    | exact resolve eq71918 eq90831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71918 eq90831
  have eq91386 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq91323
  have eq91433 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq91386
       have r₂ := eq70310
       grind)
    | exact resolve eq91386 eq70310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70310 eq91386
  have eq91453 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq89566 x
       have i₂ := eq91433
       grind)
    | exact superpose eq91433 eq89566
    | exact resolve eq89566 eq91433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89566 eq91433
  have eq91469 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq91453
  have eq91475 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq91469
       have r₂ := eq71422
       grind)
    | exact resolve eq91469 eq71422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71422 eq91469
  have eq91480 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq91475 eq20
    | exact resolve eq20 eq91475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91482 : ∀ X0 : G, (M.op (M.op (M.op y x) y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq91475 eq50
    | exact resolve eq50 eq91475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq91475
  have eq91762 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91480
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91480
    | exact resolve eq91480 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq91480
  have eq92211 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq91762 eq26
    | exact resolve eq26 eq91762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91762
  have eq101449 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq621 y x
       have i₂ := eq91482 x
       grind)
    | exact superpose eq91482 eq621
    | exact resolve eq621 eq91482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq91482
  have eq101649 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq717 x x
       have i₂ := eq101449
       grind)
    | exact superpose eq101449 eq717
    | exact resolve eq717 eq101449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq101449
  have eq101654 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq101649
  have eq101672 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101654
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq101654
    | exact resolve eq101654 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101654
  have eq102139 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq101672 eq14
    | exact resolve eq14 eq101672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101672
  have eq124882 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f124882_14 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
      intro X0
      grind
    have f124882_20 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f124882_23 : X0 ≠ (M.op (σ x) X0) := by grind
    have f124882_24 : x ≠ (M.op x y) := by grind
    have f124882_26 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 := by
      intro X0
      first
      | (have j0 := f124882_14 X0
         grind)
      | (have r₁ := f124882_14 X0
         have r₂ := f124882_24
         grind)
      | exact resolve f124882_14 f124882_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f124882_66 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f124882_20 X0 (σ x) (σ x)
         have i₂ := f124882_26 (σ x)
         grind)
      | exact superpose f124882_26 f124882_20
      | exact resolve f124882_20 f124882_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f124882_70 : X0 ≠ X0 := by
      first
      | (have i₁ := f124882_23
         have i₂ := f124882_66 X0
         grind)
      | exact superpose f124882_66 f124882_23
      | (have r₁ := f124882_23
         have r₂ := f124882_66 X0
         grind)
      | exact resolve f124882_23 f124882_66
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f124882_76 : False := by grind
    exact f124882_76
  clear eq102139
  have eq125749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124882 eq92211
    | exact resolve eq92211 eq124882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92211 eq124882
  have eq125827 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq125749
  have eq125868 : x = (M.op x y) := by
    first
    | (have r₁ := eq125827
       have r₂ := eq27
       grind)
    | exact resolve eq125827 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125827
  have eq125881 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq125868 eq20
    | exact resolve eq20 eq125868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq125885 : x ≠ x ∨ (k x y) = (M.op y x) := by
    first
    | exact superpose eq125868 eq63
    | (have r₁ := eq63
       have r₂ := eq125868
       grind)
    | exact resolve eq63 eq125868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq125892 : x ≠ x ∨ x = (k y x) := by
    first
    | exact superpose eq125868 eq123
    | (have r₁ := eq123
       have r₂ := eq125868
       grind)
    | exact resolve eq123 eq125868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq125868
  have eq126092 : x = (k y x) := by grind
  clear eq125892
  have eq126094 : (k x y) = (M.op y x) := by grind
  clear eq125885
  have eq126219 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq125881
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq125881
    | exact resolve eq125881 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125881
  have eq127158 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq126219 eq26
    | exact resolve eq26 eq126219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127163 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq126219 eq51
    | exact resolve eq51 eq126219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq127293 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq126219 eq17922
    | exact resolve eq17922 eq126219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17922
  have eq127511 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq127293
       have r₂ := eq27
       grind)
    | exact resolve eq127293 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127293
  have eq127776 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4491 x
       have i₂ := eq126092
       grind)
    | exact superpose eq126092 eq4491
    | exact resolve eq4491 eq126092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4491 eq126092
  have eq127793 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127776
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq127776
    | exact resolve eq127776 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127776
  have eq127839 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq126219 eq127793
    | exact resolve eq127793 eq126219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127793
  have eq127879 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq127839
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq127839
    | exact resolve eq127839 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127839
  have eq127914 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq26 eq127879
    | exact resolve eq127879 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq127879
  have eq127934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq126219 eq127914
    | exact resolve eq127914 eq126219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127914
  have eq127944 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq127934
       have r₂ := eq27
       grind)
    | exact resolve eq127934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127934
  have eq128094 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq126094
       grind)
    | exact superpose eq126094 eq44
    | exact resolve eq44 eq126094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq126094
  have eq128154 : (σ (M.op y x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq126219 eq128094
    | exact resolve eq128094 eq126219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128094
  have eq133398 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq127511
       have r₂ := eq127944
       grind)
    | exact resolve eq127511 eq127944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127511
  have eq133406 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq133398 eq14
    | exact resolve eq14 eq133398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133428 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq127158 eq133406
    | exact resolve eq133406 eq127158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133406
  have eq135123 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq133428 eq127163
    | exact resolve eq127163 eq133428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127163 eq133428
  have eq135157 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq135123 eq4504
    | exact resolve eq4504 eq135123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4504 eq135123
  have eq135239 : y = (k y y) := by
    first
    | exact superpose eq29 eq135157
    | exact resolve eq135157 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq135157
  have eq137320 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4028 y y
       have i₂ := eq135239
       grind)
    | exact superpose eq135239 eq4028
    | (have r₁ := eq4028 y y
       have r₂ := eq135239
       grind)
    | exact resolve eq4028 eq135239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028 eq135239
  have eq137321 : y = (M.op y y) := by grind
  clear eq137320
  have eq137391 : ∀ X0 : G, (M.op (M.op (M.op y y) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq137321
       grind)
    | exact superpose eq137321 eq14
    | exact resolve eq14 eq137321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137415 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq137391 X0
       have i₂ := eq137321
       grind)
    | exact superpose eq137321 eq137391
    | exact resolve eq137391 eq137321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137391
  have eq137426 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq137415 X0
       have i₂ := eq137321
       grind)
    | exact superpose eq137321 eq137415
    | exact resolve eq137415 eq137321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137321 eq137415
  have eq137460 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq128154
       have i₂ := eq137426 x
       grind)
    | exact superpose eq137426 eq128154
    | exact resolve eq128154 eq137426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128154 eq137426
  have eq137532 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq137460
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq137460
    | exact resolve eq137460 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq137460
  have eq137544 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq126219 eq137532
    | exact resolve eq137532 eq126219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126219 eq137532
  have eq139771 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq137544 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq137544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137544
  have eq139782 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq139771
  have eq139789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq127158 eq139782
    | exact resolve eq139782 eq127158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127158 eq139782
  have eq139802 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq139789
       have r₂ := eq27
       grind)
    | exact resolve eq139789 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq139789
  have eq139815 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq133398 eq139802
    | exact resolve eq139802 eq133398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133398 eq139802
  have eq139828 : False := by grind
  exact eq139828

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_Equation3263 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq28 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq28 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq48 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq51
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq61
  have eq180 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq186 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq180 X0 X0
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq180 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq180
  have eq665 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq186 (σ X0) (σ X1)
       grind)
    | exact superpose eq186 eq15
    | exact resolve eq15 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq186 X0 X1
       grind)
    | exact superpose eq186 eq665
    | exact resolve eq665 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq665
  have eq676 : False := by grind
  exact eq676

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation3263 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq45 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq45 (σ X0)
       grind)
    | exact superpose eq45 eq15
    | exact resolve eq15 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq59
    | exact resolve eq59 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq59
  have eq83 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq83
    | (have j0 := eq83 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq16
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq331 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq183
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq183
    | (have j1 := eq83 (σ x) (σ y)
       grind)
    | (have r₁ := eq183
       have r₂ := eq83 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq183
       have r₂ := eq83 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq183 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq183
  have eq332 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq331
  have eq335 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq332
       grind)
    | exact superpose eq332 eq16
    | exact resolve eq16 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq336 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq335
       have r₂ := eq68 x
       grind)
    | exact resolve eq335 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq372 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq336
       grind)
    | exact superpose eq336 eq10
    | exact resolve eq10 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq389 : x = y := by
    first
    | (have i₁ := eq372
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq372
    | exact resolve eq372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq433 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq389
       grind)
    | exact superpose eq389 eq16
    | exact resolve eq16 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq434 : False := by grind
  exact eq434

/-- `Equation3265`: `x ◇ x = x ◇ (y ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3265 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3265 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3265.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
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
  clear eq35
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
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
  have eq71 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq86 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq118 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq819
    | exact resolve eq819 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq823 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq820
       have r₂ := eq27
       grind)
    | exact resolve eq820 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq825 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq823
    | exact resolve eq823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq827 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq825
    | exact resolve eq825 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq830 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq827 eq51
    | (have r₁ := eq51
       have r₂ := eq827
       grind)
    | exact resolve eq51 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq835 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq830
  have eq936 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq835 eq86
    | exact resolve eq86 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq944 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq936
    | exact resolve eq936 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq936
  have eq948 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq944
       have r₂ := eq50
       grind)
    | exact resolve eq944 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1050 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq948
       grind)
    | exact superpose eq948 eq79
    | exact resolve eq79 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1051 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq948
       grind)
    | exact superpose eq948 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1052 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1051
  have eq1054 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1052
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1052
    | exact resolve eq1052 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1055 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1054
  have eq1056 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1050
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1050
    | exact resolve eq1050 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1059 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1055
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1055
    | exact resolve eq1055 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1062 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1059 eq27
    | exact resolve eq27 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1063 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1059 eq51
    | exact resolve eq51 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1059 eq71
    | (have r₁ := eq71
       have r₂ := eq1059
       grind)
    | exact resolve eq71 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1059
  have eq1068 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1065
  have eq1124 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1056 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1125 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1124
  have eq1129 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1125
    | exact resolve eq1125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1130 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1129
  have eq1135 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1130
    | exact resolve eq1130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1137 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1135 eq27
    | exact resolve eq27 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1276 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1068 eq86
    | exact resolve eq86 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq1068
  have eq1287 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1276
    | exact resolve eq1276 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1276
  have eq1292 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1287
       have r₂ := eq70
       grind)
    | exact resolve eq1287 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1300 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1292
       grind)
    | exact superpose eq1292 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1301 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1300
  have eq1303 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1301
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1301
    | exact resolve eq1301 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1304 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1303
  have eq1309 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1304
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1304
    | exact resolve eq1304 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1304
  have eq1318 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1309 eq105
    | exact resolve eq105 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1327 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1309 eq1063
    | (have r₁ := eq1063
       have r₂ := eq1309
       grind)
    | exact resolve eq1063 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063 eq1309
  have eq1333 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1327
  have eq1334 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1333
  have eq1340 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1318
  have eq1476 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1340 eq1334
    | exact resolve eq1334 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334 eq1340
  have eq1480 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1476
  have eq1484 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1480
       have r₂ := eq1062
       grind)
    | exact resolve eq1480 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq1480
  have eq1487 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1484 eq20
    | exact resolve eq20 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1489 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1484 eq50
    | (have r₁ := eq50
       have r₂ := eq1484
       grind)
    | exact resolve eq50 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1501 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1489
  have eq1510 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1487
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1487
    | exact resolve eq1487 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487
  have eq1517 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1510 eq26
    | exact resolve eq26 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1535 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1510 eq1137
    | (have r₁ := eq1137
       have r₂ := eq1510
       grind)
    | exact resolve eq1137 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1541 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1535
  have eq1542 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1541
  have eq1562 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1542 eq27
    | exact resolve eq27 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1585 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq1501
       grind)
    | exact superpose eq1501 eq79
    | exact resolve eq79 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1591 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1585
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1585
    | exact resolve eq1585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq1597 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1517 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1517
       grind)
    | exact resolve eq12 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1597
       have r₂ := eq1542
       grind)
    | exact resolve eq1597 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542 eq1597
  have eq1608 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1607
       have r₂ := eq27
       grind)
    | exact resolve eq1607 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq1609 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1510 eq1591
    | exact resolve eq1591 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510 eq1591
  have eq1631 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1609
  have eq1747 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1631 eq1608
    | exact resolve eq1608 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608 eq1631
  have eq1751 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1747
  have eq1755 : x = (M.op x y) := by
    first
    | (have r₁ := eq1751
       have r₂ := eq1562
       grind)
    | exact resolve eq1751 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq1751
  have eq1759 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1755 eq20
    | exact resolve eq20 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1761 : x ≠ y ∨ x = (k y x) := by
    first
    | exact superpose eq1755 eq50
    | exact resolve eq50 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1763 : x ≠ x ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq1755 eq70
    | (have r₁ := eq70
       have r₂ := eq1755
       grind)
    | exact resolve eq70 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1774 : y = (k y x) ∨ x = y := by grind
  clear eq1763
  have eq1784 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1759
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1759
    | exact resolve eq1759 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq1786 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1784 eq26
    | exact resolve eq26 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2131 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq1774
       grind)
    | exact superpose eq1774 eq79
    | exact resolve eq79 eq1774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1774
  have eq2140 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1784 eq2131
    | exact resolve eq2131 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq2144 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq2140
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2140
    | exact resolve eq2140 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2140
  have eq2154 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2144 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2155 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq2154
  have eq2158 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1786 eq2155
    | exact resolve eq2155 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq2161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1786 eq2158
    | exact resolve eq2158 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2158
  have eq2164 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq2161
       have r₂ := eq27
       grind)
    | exact resolve eq2161 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq2170 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq2164 eq27
    | exact resolve eq27 eq2164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2171 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2164 eq51
    | (have r₁ := eq51
       have r₂ := eq2164
       grind)
    | exact resolve eq51 eq2164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2164
  have eq2180 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq2171
  have eq2183 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1784 eq2180
    | exact resolve eq2180 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq2206 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2183 eq2144
    | exact resolve eq2144 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2144
  have eq2207 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2183 eq118
    | exact resolve eq118 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq2183
  have eq2210 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq2206
  have eq2215 : (τ (σ (M.op x y))) = (k y x) ∨ x = y := by
    first
    | exact superpose eq1755 eq2207
    | exact resolve eq2207 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq2216 : x = y := by
    first
    | (have r₁ := eq2210
       have r₂ := eq2170
       grind)
    | exact resolve eq2210 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170 eq2210
  have eq2220 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq2215
    | exact resolve eq2215 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2215
  have eq2223 : x = (k y x) ∨ x = y := by
    first
    | exact superpose eq1755 eq2220
    | exact resolve eq2220 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755 eq2220
  have eq2225 : x = (k y x) := by
    first
    | (have r₁ := eq2223
       have r₂ := eq1761
       grind)
    | exact resolve eq2223 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761 eq2223
  have eq2227 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2216
       grind)
    | exact superpose eq2216 eq24
    | exact resolve eq24 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2257 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2227
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2227
    | exact resolve eq2227 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq2267 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1784 eq2257
    | exact resolve eq2257 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq2295 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2267 eq1786
    | exact resolve eq1786 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786 eq2267
  have eq2321 : x = (k x x) := by
    first
    | (have i₁ := eq2225
       have i₂ := eq2216
       grind)
    | exact superpose eq2216 eq2225
    | exact resolve eq2225 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216 eq2225
  have eq2324 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2321
       grind)
    | exact superpose eq2321 eq43
    | exact resolve eq43 eq2321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2321
  have eq2328 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1784 eq2324
    | exact resolve eq2324 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2324
  have eq2329 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2328
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2328
    | exact resolve eq2328 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2328
  have eq2330 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1784 eq2329
    | exact resolve eq2329 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1784 eq2329
  have eq2607 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2330 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330
  have eq2608 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2607
  have eq2645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2295 eq2608
    | exact resolve eq2608 eq2295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295 eq2608
  have eq2646 : False := by grind
  exact eq2646

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  clear eq24 eq35
  have eq50 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 X4
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X1 X3) ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X0 X2)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : x ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
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
  have eq84 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq44
    | (have j1 := eq91 x y
       grind)
    | exact resolve eq44 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq130 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq133 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq130
    | exact resolve eq130 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq134 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq133
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133
    | exact resolve eq133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq134 eq91
    | (have j0 := eq91 (σ x) (σ y)
       grind)
    | exact resolve eq91 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq201
    | exact resolve eq201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq205 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq202
       have r₂ := eq27
       grind)
    | exact resolve eq202 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq207 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq205
    | exact resolve eq205 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq209 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq207 eq27
    | exact resolve eq27 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq91 (σ X0) sF3
       grind)
    | exact superpose eq91 eq40
    | (have j1 := eq91 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq91
  have eq275 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq207 eq52
    | exact resolve eq52 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq328 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq275 eq55
    | exact resolve eq55 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq329 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq55 x X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq358 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X0
       have i₂ := eq328 sF2
       grind)
    | exact superpose eq328 eq328
    | exact resolve eq328 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq387 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq358 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq1517 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq207 eq84
    | (have r₁ := eq84
       have r₂ := eq207
       grind)
    | exact resolve eq84 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq207
  have eq1518 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1517
  have eq1737 : ∀ X0 X1 X2 X3 X5 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X2)))) ≠ (M.op X3 X5) ∨ (k X5 X3) = (M.op X5 X3) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq70 X1 X3 (M.op X3 x) X5
       have i₂ := eq50 X3 X1 x X0 X2
       grind)
    | (have i₁ := eq70 X1 X3 (M.op X3 x) X5
       have i₂ := eq50 X0 X1 X2 X3 x
       grind)
    | exact superpose eq50 eq70
    | (have j0 := eq70 X0 X3 X2 X5
       grind)
    | (have r₁ := eq70 X0 X3 X2 (M.op X3 (M.op X3 x))
       have r₂ := eq50 X0 X3 X2 X3 x
       grind)
    | (have r₁ := eq70 X3 X0 x (M.op X0 (M.op X0 X2))
       have r₂ := eq50 X0 X0 X2 X3 x
       grind)
    | exact resolve eq70 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq70
  have eq1813 : ∀ X0 X3 X5 : G, (M.op X0 X0) ≠ (M.op X3 X5) ∨ (k X5 X3) = (M.op X5 X3) := by
    intro X0 X3 X5
    first
    | (have i₁ := eq1737 X0 x x X3 X5
       have i₂ := eq14 X0 x (M.op X0 x)
       grind)
    | exact superpose eq14 eq1737
    | (have j0 := eq1737 X0 x x X3 X5
       grind)
    | (have r₁ := eq1737 X0 x x X0 X0
       have r₂ := eq14 X0 x (M.op X0 x)
       grind)
    | exact resolve eq1737 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq32508 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq224 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq145207 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1518
       have i₂ := eq329 sF3 x
       grind)
    | (have i₁ := eq1518
       have i₂ := eq329 X0 sF3
       grind)
    | exact superpose eq329 eq1518
    | exact resolve eq1518 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq149611 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq145207 eq1813
    | (have j0 := eq1813 X0 X1 X1
       grind)
    | (have r₁ := eq1813 X0 (σ y) (σ x)
       have r₂ := eq145207 X0
       grind)
    | exact resolve eq1813 eq145207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145207
  have eq149988 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq149611 x x
       have r₂ := eq387 x x
       grind)
    | (have r₁ := eq149611 x x
       have r₂ := eq387 x x
       grind)
    | exact resolve eq149611 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq149611
  have eq150113 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq149988
    | exact resolve eq149988 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149988
  have eq150163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq134 eq150113
    | exact resolve eq150113 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq150113
  have eq150181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq150163
  have eq150185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq150181
       have r₂ := eq209
       grind)
    | exact resolve eq150181 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq150181
  have eq150186 : x = (M.op x y) := by
    first
    | (have r₁ := eq150185
       have r₂ := eq27
       grind)
    | exact resolve eq150185 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150185
  have eq150646 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq150186 eq20
    | exact resolve eq20 eq150186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq150650 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq150186 eq83
    | (have r₁ := eq83
       have r₂ := eq150186
       grind)
    | exact resolve eq83 eq150186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq150741 : (M.op y x) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq150650
  have eq150807 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq150646
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq150646
    | exact resolve eq150646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150646
  have eq232739 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq150741
       have i₂ := eq329 y X0
       grind)
    | (have i₁ := eq150741
       have i₂ := eq329 X0 y
       grind)
    | exact superpose eq329 eq150741
    | exact resolve eq150741 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150741
  have eq237606 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1813 X0 y x
       have i₂ := eq232739 X1
       grind)
    | exact superpose eq232739 eq1813
    | (have j0 := eq1813 X0 X1 X1
       grind)
    | (have r₁ := eq1813 X0 y x
       have r₂ := eq232739 X0
       grind)
    | exact resolve eq1813 eq232739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813 eq232739
  have eq237618 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq237606 x x
       have r₂ := eq329 x x
       grind)
    | (have r₁ := eq237606 x x
       have r₂ := eq329 x x
       grind)
    | exact resolve eq237606 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq237606
  have eq237803 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq237618
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq237618
    | exact resolve eq237618 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq237618
  have eq237873 : x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq150186 eq237803
    | exact resolve eq237803 eq150186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150186 eq237803
  have eq237874 : x = (k x y) := by grind
  clear eq237873
  have eq237914 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32508 x
       have i₂ := eq237874
       grind)
    | exact superpose eq237874 eq32508
    | (have j0 := eq32508 x
       grind)
    | exact resolve eq32508 eq237874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32508 eq237874
  have eq237928 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq237914
  have eq237943 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq237928
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq237928
    | exact resolve eq237928 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq237928
  have eq237965 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq237943
    | exact resolve eq237943 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq237943
  have eq237986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq150807 eq237965
    | exact resolve eq237965 eq150807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150807 eq237965
  have eq238005 : False := by grind
  exact eq238005

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X0 X2)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X1 X3) ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X0 X2)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X1 X3) ∨ (k X3 X1) = (M.op X3 X1) ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq14
    | (have j0 := eq14 X3 X1
       grind)
    | exact resolve eq14 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 X3 : G, (k X3 X1) = (M.op X3 X1) ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq32 X0 X1 X2 X3
       have j1 := eq27 X0 X1 X2 X3
       grind)
    | (have r₁ := eq32 X0 X1 X2 X3
       have r₂ := eq27 X0 X1 X2 X3
       grind)
    | (have r₁ := eq32 X1 X0 X2 (M.op X1 (M.op X0 X2))
       have r₂ := eq27 X0 X1 X2 (M.op X0 (M.op X1 X2))
       grind)
    | (have r₁ := eq32 X0 X1 X2 (M.op X1 X3)
       have r₂ := eq27 X0 X1 X2 X3
       grind)
    | exact resolve eq32 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 x X0
       have i₂ := eq23 x X1
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq78 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq26 X0 X1 X2
       grind)
    | (have r₁ := eq26 X0 X1 X2
       have r₂ := eq60 X0 X1
       grind)
    | (have r₁ := eq26 X1 X0 X2
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq26 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq60
  have eq362 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq78 X0 x (M.op X0 X2)
       have i₂ := eq48 X0 x X2 x
       grind)
    | (have i₁ := eq78 X0 x X2
       have i₂ := eq48 X0 x X2 (M.op X0 (M.op x X2))
       grind)
    | exact superpose eq48 eq78
    | (have j1 := eq48 X0 X2 X2 X0
       grind)
    | exact resolve eq78 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq78
  have eq373 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) := by
    intro X0 X2
    first
    | (have j0 := eq362 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq609 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq373 (σ X0) (σ X1)
       grind)
    | exact superpose eq373 eq15
    | exact resolve eq15 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 X1
       have i₂ := eq373 X0 X1
       grind)
    | exact superpose eq373 eq609
    | exact resolve eq609 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq609
  have eq615 : False := by grind
  exact eq615
