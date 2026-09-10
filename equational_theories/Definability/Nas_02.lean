import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_y_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq92 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq463 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq446 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq446
    | (have j0 := eq446 X0 X1
       grind)
    | exact resolve eq446 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq446
  have eq687 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq463 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq463
    | exact resolve eq463 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq715 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq687 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq687
    | (have j0 := eq687 X0 X1
       grind)
    | exact resolve eq687 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq722 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq715 X0 X1
       have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq715 X1 X0
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq715 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq715
  have eq725 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq722
    | exact resolve eq722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq786 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq725 X0 (τ X1)
       grind)
    | exact superpose eq725 eq17
    | (have j1 := eq725 X0 (τ X1)
       grind)
    | exact resolve eq17 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq786 X0 X1
       grind)
    | exact superpose eq786 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq786 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq786 X0 X1
       grind)
    | exact resolve eq13 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) X0
       have i₂ := eq786 X0 X1
       grind)
    | exact superpose eq786 eq12
    | (have j1 := eq786 X0 X1
       grind)
    | exact resolve eq12 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq920 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq908 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq929 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq920 X0 X1
       have j1 := eq910 X0 X1
       grind)
    | (have r₁ := eq920 X0 X1
       have r₂ := eq910 X0 X1
       grind)
    | exact resolve eq920 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq920
  have eq1045 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq929
    | exact resolve eq929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq929 X0 X1
       grind)
    | exact superpose eq929 eq17
    | (have j1 := eq929 X0 X1
       grind)
    | exact resolve eq17 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq929
  have eq1098 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1045 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1045
    | (have j0 := eq1045 X0 X1
       grind)
    | exact resolve eq1045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1116 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq1098 X1 X0
       grind)
    | exact superpose eq1098 eq10
    | (have j1 := eq1098 X1 X0
       grind)
    | exact resolve eq10 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1158 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1116 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq1116
    | (have j0 := eq1116 X0 X1
       grind)
    | exact resolve eq1116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1194 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1158 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1949 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1062 X0 X1
       have i₂ := eq725 (σ X0) X1
       grind)
    | exact superpose eq725 eq1062
    | (have j1 := eq725 (σ X0) X1
       grind)
    | exact resolve eq1062 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1985 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq2800 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1985 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1985
    | exact resolve eq1985 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2810 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x (τ (σ y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1985 x (σ y)
       grind)
    | exact superpose eq1985 eq16
    | (have j1 := eq1985 x (σ y)
       grind)
    | exact resolve eq16 eq1985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1985
  have eq2862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq2810
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2810
    | exact resolve eq2810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810
  have eq2872 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have r₁ := eq2862
       have r₂ := eq16
       grind)
    | exact resolve eq2862 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq2922 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X1))
       have i₂ := eq2800 X0 X1
       grind)
    | exact superpose eq2800 eq10
    | (have j1 := eq2800 X0 X1
       grind)
    | exact resolve eq10 eq2800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2800
  have eq2988 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (τ (M.op X1 (σ X0))) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2922 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2922
    | (have j0 := eq2922 X1 (σ X0)
       grind)
    | exact resolve eq2922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922
  have eq3193 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1194 (σ X1) X0
       have i₂ := eq2988 X1 X0
       grind)
    | exact superpose eq2988 eq1194
    | (have j0 := eq1194 (σ X1) X0
       have j1 := eq2988 X1 X0
       grind)
    | (have r₁ := eq1194 (σ X0) X1
       have r₂ := eq2988 X0 X1
       grind)
    | exact resolve eq1194 eq2988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq2988
  have eq3210 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193
  have eq3322 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq3210 (σ X0) X1
       grind)
    | exact superpose eq3210 eq22
    | (have j1 := eq3210 (σ X0) X1
       grind)
    | exact resolve eq22 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3210
  have eq3344 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3322 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3322
    | (have j0 := eq3322 X0 X1
       grind)
    | exact resolve eq3322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322
  have eq3358 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3344 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3344
    | (have j0 := eq3344 X0 X1
       grind)
    | exact resolve eq3344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq3365 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3358 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3358
    | (have j0 := eq3358 X0 X1
       grind)
    | exact resolve eq3358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq3477 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 X1
       have i₂ := eq3365 X0 X1
       grind)
    | exact superpose eq3365 eq725
    | (have j0 := eq725 X0 X1
       have j1 := eq3365 X0 X1
       grind)
    | exact resolve eq725 eq3365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq3365
  have eq3513 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3477 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477
  have eq3593 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq3513 X0 X1
       grind)
    | exact superpose eq3513 eq11
    | (have j1 := eq3513 X0 X1
       grind)
    | exact resolve eq11 eq3513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3513
  have eq3689 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3593 x y
       grind)
    | exact superpose eq3593 eq16
    | (have j1 := eq3593 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3593 x y
       grind)
    | exact resolve eq16 eq3593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593
  have eq3719 : x = (M.op x y) := by grind
  clear eq3689
  have eq3747 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2872
       have i₂ := eq3719
       grind)
    | exact superpose eq3719 eq2872
    | exact resolve eq2872 eq3719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872 eq3719
  have eq3763 : False := by grind
  exact eq3763

/-- `Equation2420`: `x = (y ◇ (z ◇ (w ◇ y))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pxx_pxy_Equation2420 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2420 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2420.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X3 X1))) X0) = X0 := by
    intro X0 X1 X2 X3
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
  have eq52 : ∀ X0 X1 X5 : G, (M.op (M.op X0 (M.op X1 X0)) X5) = X5 := by
    intro X0 X1 X5
    first
    | (have i₁ := eq14 X5 X0 X1 (M.op x (M.op x (M.op x x)))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq77 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq88 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq81
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq98 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq98
  have eq246 : ∀ X0 X4 : G, (M.op (M.op X0 X0) X4) = X4 := by
    intro X0 X4
    first
    | (have i₁ := eq52 X0 (M.op x (M.op x (M.op x x))) X4
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq275 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq246 X0 (M.op X0 X0)
       grind)
    | exact superpose eq246 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq246 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq541 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq75 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq551 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq541 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq556 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq551 X0 X1
       have j1 := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq551 X0 X1
       have r₂ := eq13 (σ X0) X1
       grind)
    | exact resolve eq551 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq6669 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq6706 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49 eq6669
    | exact resolve eq6669 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6669
  have eq6709 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq6706
       have r₂ := eq13 x x
       grind)
    | exact resolve eq6706 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6706
  have eq6711 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq6709
       grind)
    | exact superpose eq6709 eq43
    | exact resolve eq43 eq6709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7312 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (σ (M.op X0 X0)) X1) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq556 (M.op X0 X0) X1
       have i₂ := eq283 X0 (M.op X0 X0)
       grind)
    | exact superpose eq283 eq556
    | (have j0 := eq556 (M.op X0 X0) X1
       grind)
    | exact resolve eq556 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq7347 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ (M.op X0 X0)) X1) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7312 X0 X1
       have i₂ := eq246 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq7312 X0 X1
       have i₂ := eq246 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq246 eq7312
    | (have j0 := eq7312 X0 X1
       grind)
    | exact resolve eq7312 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7312
  have eq7348 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq7347 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7347
  have eq10352 : (M.op y y) = (τ (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq16
    | exact resolve eq16 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq10396 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq103 eq10352
    | exact resolve eq10352 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10352
  have eq10401 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq10396
       have r₂ := eq13 y x
       grind)
    | exact resolve eq10396 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10396
  have eq11003 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq11023 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11003
  have eq11026 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11023
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq11023
    | exact resolve eq11023 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq11023
  have eq11050 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq11026
       have r₂ := eq13 (σ x) x
       grind)
    | exact resolve eq11026 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11026
  have eq11066 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq11050 eq49
    | exact resolve eq49 eq11050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq11098 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq11066
       have i₂ := eq6709
       grind)
    | exact superpose eq6709 eq11066
    | exact resolve eq11066 eq6709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6709 eq11066
  have eq11365 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  clear eq77
  have eq11384 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq11365
  have eq11386 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11384
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq11384
    | exact resolve eq11384 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq11384
  have eq11414 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq11386
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq11386 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11386
  have eq11443 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq11414 eq103
    | exact resolve eq103 eq11414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq11414
  have eq11470 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq11443
       have i₂ := eq10401
       grind)
    | exact superpose eq10401 eq11443
    | exact resolve eq11443 eq10401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10401 eq11443
  have eq46672 : ∀ X0 : G, (σ (k (M.op X0 X0) x)) = (M.op (σ x) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq39 (M.op X0 X0)
       have i₂ := eq7348 X0 sF2
       grind)
    | exact superpose eq7348 eq39
    | exact resolve eq39 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq7348
  have eq46678 : ∀ X0 : G, (M.op (σ x) (σ (M.op X0 X0))) = (σ (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq46672 X0
       have i₂ := eq283 X0 x
       grind)
    | exact superpose eq283 eq46672
    | exact resolve eq46672 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq46672
  have eq51682 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq51683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq51682
    | exact resolve eq51682 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51682
  have eq51694 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq51683
       have r₂ := eq27
       grind)
    | exact resolve eq51683 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51683
  have eq51701 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq51694 eq11470
    | exact resolve eq11470 eq51694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11470 eq51694
  have eq51769 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq51701
    | exact resolve eq51701 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq51701
  have eq51770 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq51769
  have eq51778 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq51770 eq11098
    | exact resolve eq11098 eq51770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11098 eq51770
  have eq51845 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq51778
    | exact resolve eq51778 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq51778
  have eq51846 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq51845
  have eq51873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq46678 y
       have i₂ := eq51846
       grind)
    | exact superpose eq51846 eq46678
    | exact resolve eq46678 eq51846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46678 eq51846
  have eq51920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq51873
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51873
    | exact resolve eq51873 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51873
  have eq51930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq51920
    | exact resolve eq51920 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51920
  have eq51936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq51930
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51930
    | exact resolve eq51930 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51930
  have eq51937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq51936
    | exact resolve eq51936 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51936
  have eq51938 : x = (M.op x x) := by
    first
    | (have r₁ := eq51937
       have r₂ := eq27
       grind)
    | exact resolve eq51937 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51937
  have eq52613 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6711
       have i₂ := eq51938
       grind)
    | exact superpose eq51938 eq6711
    | exact resolve eq6711 eq51938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6711
  have eq52626 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq246 x X0
       have i₂ := eq51938
       grind)
    | exact superpose eq51938 eq246
    | exact resolve eq246 eq51938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51938
  have eq52695 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11050 eq52613
    | exact resolve eq52613 eq11050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11050 eq52613
  have eq52701 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq52695
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52695
    | exact resolve eq52695 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq52695
  have eq52704 : y = (M.op x y) := by
    first
    | (have i₁ := eq52626 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52626
    | (have j0 := eq52626 y
       grind)
    | exact resolve eq52626 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq52626
  have eq53032 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq52704 eq20
    | exact resolve eq20 eq52704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq52704
  have eq53205 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq53032
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq53032
    | exact resolve eq53032 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq53032
  have eq53580 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq52701 eq246
    | exact resolve eq246 eq52701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq52701
  have eq53677 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53580 eq26
    | (have j1 := eq53580 (σ y)
       grind)
    | exact resolve eq26 eq53580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53580
  have eq53986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53205 eq53677
    | exact resolve eq53677 eq53205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53205 eq53677
  have eq54004 : False := by grind
  exact eq54004

/-- `Equation2449`: `x = (x ◇ ((x ◇ y) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation2449 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2449 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2449.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq10
    | exact resolve eq10 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq92 X1 X0
       grind)
    | exact superpose eq92 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq92 X1 X0
       grind)
    | exact resolve eq12 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq270 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq257 X0 X1
       have j1 := eq79 X0 (σ X1)
       grind)
    | (have r₁ := eq257 X0 X0
       have r₂ := eq79 X0 (σ X0)
       grind)
    | (have r₁ := eq257 X0 X1
       have r₂ := eq79 X0 (σ X1)
       grind)
    | exact resolve eq257 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq280 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq245 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq245
    | (have j0 := eq245 X0 X1
       grind)
    | exact resolve eq245 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq281 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq285 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq286 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq289 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq527 : ∀ X0 X1 : G, (k (σ (σ X1)) X0) = (σ (M.op (τ X0) (σ X1))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (τ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ X1)
       have i₂ := eq285 (τ X0) X1
       grind)
    | exact superpose eq285 eq18
    | (have j1 := eq285 (τ X0) X1
       grind)
    | exact resolve eq18 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq285
  have eq532 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (σ X1)) ∨ (k (σ (σ X1)) X0) = (σ (M.op (τ X0) (σ X1))) ∨ (σ (M.op X1 X1)) = (M.op (τ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq527
    | (have j0 := eq527 X0 X1
       grind)
    | exact resolve eq527 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq907 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq289 (τ X1) (τ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq289
    | (have j0 := eq289 (τ X0) (τ X1)
       grind)
    | exact resolve eq289 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq907 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq907
    | (have j0 := eq907 X0 X1
       grind)
    | exact resolve eq907 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq937 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq925 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq925
    | (have j0 := eq925 X0 X1
       grind)
    | exact resolve eq925 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq943 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq937 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq937
    | (have j0 := eq937 X0 X1
       grind)
    | exact resolve eq937 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq946 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq943 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq943
    | (have j0 := eq943 X0 X1
       grind)
    | exact resolve eq943 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq947 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq946 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq946
    | (have j0 := eq946 X0 X1
       grind)
    | exact resolve eq946 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq948 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq947 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq947
    | (have j0 := eq947 X0 X1
       grind)
    | exact resolve eq947 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq949 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq948 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq948
    | (have j0 := eq948 X0 X1
       grind)
    | exact resolve eq948 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1274 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq263 (τ X1) (τ X0)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq263
    | (have j0 := eq263 (τ X1) (τ X0)
       grind)
    | exact resolve eq263 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1302 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1274 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq1274
    | (have j0 := eq1274 X0 X1
       grind)
    | exact resolve eq1274 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1319 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1302 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1302
    | (have j0 := eq1302 X0 X1
       grind)
    | exact resolve eq1302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1329 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1319 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1319
    | (have j0 := eq1319 X0 X1
       grind)
    | exact resolve eq1319 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1336 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1329 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1329
    | (have j0 := eq1329 X0 X1
       grind)
    | exact resolve eq1329 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq1341 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1336 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq1336
    | (have j0 := eq1336 X0 X1
       grind)
    | exact resolve eq1336 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1345 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1341 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1341
    | (have j0 := eq1341 X0 X1
       grind)
    | exact resolve eq1341 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1349 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1345 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1345
    | (have j0 := eq1345 X0 X1
       grind)
    | exact resolve eq1345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq1351 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1349 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq1349
    | (have j0 := eq1349 X0 X1
       grind)
    | exact resolve eq1349 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1583 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq264 (τ X1) (τ X0)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq264
    | (have j0 := eq264 (τ X1) (τ X0)
       grind)
    | exact resolve eq264 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq1615 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1583 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1583
    | (have j0 := eq1583 X0 X1
       grind)
    | exact resolve eq1583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1632 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1615 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq1615
    | (have j0 := eq1615 X0 X1
       grind)
    | exact resolve eq1615 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615
  have eq1646 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1632 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1632
    | (have j0 := eq1632 X0 X1
       grind)
    | exact resolve eq1632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1655 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1646 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1646
    | (have j0 := eq1646 X0 X1
       grind)
    | exact resolve eq1646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1662 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1655 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq1655
    | (have j0 := eq1655 X0 X1
       grind)
    | exact resolve eq1655 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq1668 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1662 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1662
    | (have j0 := eq1662 X0 X1
       grind)
    | exact resolve eq1662 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662
  have eq1672 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1668 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1668
    | (have j0 := eq1668 X0 X1
       grind)
    | exact resolve eq1668 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1674 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1672 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq1672
    | (have j0 := eq1672 X0 X1
       grind)
    | exact resolve eq1672 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq5722 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (M.op (τ X1) (τ X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1351 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq1351
    | (have j0 := eq1351 (τ X0) (τ X1)
       grind)
    | exact resolve eq1351 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq5751 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X1 X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5722 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq5722
    | (have j0 := eq5722 X0 X1
       grind)
    | exact resolve eq5722 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5722
  have eq5765 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) ≠ (τ (M.op X1 X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5751 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq5751
    | (have j0 := eq5751 X0 X1
       grind)
    | exact resolve eq5751 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5751
  have eq5775 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X1 X1)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5765 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq5765
    | (have j0 := eq5765 X0 X1
       grind)
    | exact resolve eq5765 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5765
  have eq5846 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (τ (k X0 X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1674 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq1674
    | (have j0 := eq1674 (τ X0) (τ X1)
       grind)
    | exact resolve eq1674 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq5871 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5846 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq5846
    | (have j0 := eq5846 X0 X1
       grind)
    | exact resolve eq5846 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5846
  have eq5883 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5871 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq5871
    | (have j0 := eq5871 X0 X1
       grind)
    | exact resolve eq5871 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5871
  have eq5895 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5883 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq5883
    | (have j0 := eq5883 X0 X1
       grind)
    | exact resolve eq5883 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5883
  have eq12566 : ∀ X0 X1 : G, (k (σ (σ X1)) X0) = (σ (M.op (τ X0) (σ X1))) ∨ (M.op X0 X0) = (σ (M.op (τ X0) (σ X1))) ∨ (σ (M.op X1 X1)) = (M.op (τ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq532 X0 X1
       grind)
    | exact superpose eq532 eq11
    | (have j1 := eq532 X0 X1
       grind)
    | exact resolve eq11 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq553495 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op X1 X1) = (σ (M.op (τ X1) X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12566 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12566
    | exact resolve eq12566 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12566
  have eq554170 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq553495 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq553495
    | (have j0 := eq553495 X0 X1
       grind)
    | exact resolve eq553495 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553495
  have eq554224 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554170 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq554170
    | exact resolve eq554170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554282 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) X0)
       have i₂ := eq554170 X0 X1
       grind)
    | exact superpose eq554170 eq10
    | (have j1 := eq554170 X0 X1
       grind)
    | exact resolve eq10 eq554170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554561 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (σ X1) X0) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq554170 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554170
  have eq554573 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (τ X1) X0) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq554282 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq554282
    | (have j0 := eq554282 X0 X1
       grind)
    | exact resolve eq554282 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq554282
  have eq554595 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554224 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq554224
    | (have j0 := eq554224 X0 X1
       grind)
    | exact resolve eq554224 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554224
  have eq554606 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq554595 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq554595
    | (have j0 := eq554595 X0 X1
       grind)
    | exact resolve eq554595 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554595
  have eq554648 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op (τ (σ X0)) X1) ∨ (σ (M.op X0 X0)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554561 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq554561
    | (have j0 := eq554561 (σ X0) X1
       grind)
    | exact resolve eq554561 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554561
  have eq554962 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op (τ (σ X0)) X1) ∨ (σ (M.op X0 X0)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554648 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq554648
    | (have j0 := eq554648 X0 X1
       grind)
    | exact resolve eq554648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554648
  have eq554990 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554962 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq554962
    | (have j0 := eq554962 X0 X1
       grind)
    | exact resolve eq554962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554962
  have eq555012 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554990 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq554990
    | (have j0 := eq554990 X0 X1
       grind)
    | exact resolve eq554990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554990
  have eq562686 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (τ X1)
       have i₂ := eq554573 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq554573 X0 X1
       grind)
    | exact superpose eq554573 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq554573 X0 X1
       grind)
    | (have r₁ := eq12 X0 (τ X1)
       have r₂ := eq554573 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) (τ X1)
       have r₂ := eq554573 (τ X1) X1
       grind)
    | exact resolve eq12 eq554573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554573
  have eq562748 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq562686 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562686
  have eq562783 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (k X0 (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq562748 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq562748
    | (have j0 := eq562748 X0 X1
       grind)
    | exact resolve eq562748 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562748
  have eq569256 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq562783 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq562783
    | exact resolve eq562783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562783
  have eq570279 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq569256 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq569256
    | (have j0 := eq569256 X0 X1
       grind)
    | exact resolve eq569256 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569256
  have eq570372 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq570279 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq570279
    | (have j0 := eq570279 X0 X1
       grind)
    | exact resolve eq570279 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570279
  have eq570440 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq570372 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq570372
    | (have j0 := eq570372 X0 X1
       grind)
    | exact resolve eq570372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570372
  have eq571089 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X1)
       have i₂ := eq570440 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq570440 X0 X1
       grind)
    | exact superpose eq570440 eq10
    | (have j1 := eq570440 X0 X1
       grind)
    | exact resolve eq10 eq570440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570440
  have eq571450 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq571089 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq571089
    | (have j0 := eq571089 X0 X1
       grind)
    | exact resolve eq571089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571089
  have eq574414 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq571450 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq571450 X0 X1
       grind)
    | exact superpose eq571450 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq571450 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq571450 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq571450 X1 X1
       grind)
    | exact resolve eq13 eq571450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574443 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 X0
       have i₂ := eq571450 X0 (σ X1)
       grind)
    | (have i₁ := eq79 X0 (σ X0)
       have i₂ := eq571450 (σ X0) X1
       grind)
    | exact superpose eq571450 eq79
    | (have j0 := eq79 X1 X0
       have j1 := eq571450 X0 (σ X1)
       grind)
    | exact resolve eq79 eq571450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq574448 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X1 X0
       have i₂ := eq571450 X0 (τ X1)
       grind)
    | (have i₁ := eq143 X0 (τ X0)
       have i₂ := eq571450 (τ X0) X1
       grind)
    | exact superpose eq571450 eq143
    | (have j0 := eq143 X1 X0
       have j1 := eq571450 X0 (τ X1)
       grind)
    | exact resolve eq143 eq571450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq571450
  have eq575046 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq574448 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574448
  have eq575051 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq574443 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574443
  have eq575052 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq574414 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574414
  have eq722014 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq575052 X0 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq575052
    | (have j0 := eq575052 X1 (σ X0)
       grind)
    | exact resolve eq575052 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722018 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq575052 X0 (τ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq575052
    | (have j0 := eq575052 X1 (τ X0)
       grind)
    | exact resolve eq575052 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575052
  have eq723116 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq722018 X0 X1
       have j1 := eq575046 X1 X0
       grind)
    | (have r₁ := eq722018 X1 X0
       have r₂ := eq575046 X0 X1
       grind)
    | exact resolve eq722018 eq575046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575046 eq722018
  have eq723119 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq722014 X0 X1
       have j1 := eq575051 X1 X0
       grind)
    | (have r₁ := eq722014 X1 X0
       have r₂ := eq575051 X0 X1
       grind)
    | exact resolve eq722014 eq575051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575051 eq722014
  have eq725029 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq723116 X1 (τ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq723116
    | exact resolve eq723116 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725113 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq723116 X1 X0
       grind)
    | exact superpose eq723116 eq17
    | (have j1 := eq723116 X1 X0
       grind)
    | exact resolve eq17 eq723116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq723116
  have eq726701 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ (k X0 X1)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq725029 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq725029
    | (have j0 := eq725029 X0 X1
       grind)
    | exact resolve eq725029 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725029
  have eq735171 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X1))) = (k (τ (σ X1)) X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq723119 X1 (σ X0)
       grind)
    | exact superpose eq723119 eq23
    | (have j1 := eq723119 X1 (σ X0)
       grind)
    | exact resolve eq23 eq723119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq723119
  have eq736074 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq735171 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq735171
    | (have j0 := eq735171 X0 X1
       grind)
    | exact resolve eq735171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735171
  have eq736370 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq736074 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq736074
    | (have j0 := eq736074 X0 X1
       grind)
    | exact resolve eq736074 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736074
  have eq736466 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq736370 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq736370
    | (have j0 := eq736370 X0 X1
       grind)
    | exact resolve eq736370 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736370
  have eq736541 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq736466 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq736466
    | (have j0 := eq736466 X0 X1
       grind)
    | exact resolve eq736466 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736466
  have eq748835 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq725113 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq725113
    | exact resolve eq725113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725113
  have eq749471 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq748835 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq748835
    | (have j0 := eq748835 X0 X1
       grind)
    | exact resolve eq748835 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748835
  have eq749540 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq749471 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq749471
    | (have j0 := eq749471 X0 X1
       grind)
    | exact resolve eq749471 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749471
  have eq749581 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq749540 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq749540
    | (have j0 := eq749540 X0 X1
       grind)
    | exact resolve eq749540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749540
  have eq827143 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq736541 X1 X0
       grind)
    | exact superpose eq736541 eq10
    | (have j1 := eq736541 X1 X0
       grind)
    | exact resolve eq10 eq736541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736541
  have eq827576 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq827143 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq827143
    | (have j0 := eq827143 X0 X1
       grind)
    | exact resolve eq827143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827143
  have eq830643 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq827576 (τ X1) (τ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq827576
    | exact resolve eq827576 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq831864 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (k X0 X1))) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq827576 X0 X1
       grind)
    | exact superpose eq827576 eq10
    | (have j1 := eq827576 X0 X1
       grind)
    | exact resolve eq10 eq827576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827576
  have eq832308 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq831864 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq831864
    | (have j0 := eq831864 X0 X1
       grind)
    | exact resolve eq831864 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831864
  have eq832974 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq830643 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq830643
    | (have j0 := eq830643 X0 X1
       grind)
    | exact resolve eq830643 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq830643
  have eq833554 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq832974 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq832974
    | (have j0 := eq832974 X0 X1
       grind)
    | exact resolve eq832974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832974
  have eq834042 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq833554 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq833554
    | (have j0 := eq833554 X0 X1
       grind)
    | exact resolve eq833554 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq833554
  have eq834283 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (τ (k X0 X1)) = (τ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq834042 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq834042
    | (have j0 := eq834042 X0 X1
       grind)
    | exact resolve eq834042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834042
  have eq834403 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ (k X0 X1)) = (τ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq834283 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq834283
    | (have j0 := eq834283 X0 X1
       grind)
    | exact resolve eq834283 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834283
  have eq836778 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq832308 X0 X1
       grind)
    | exact superpose eq832308 eq11
    | (have j1 := eq832308 X0 X1
       grind)
    | exact resolve eq11 eq832308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832308
  have eq838671 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y x) = (M.op y y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq836778 y x
       grind)
    | exact superpose eq836778 eq16
    | (have j1 := eq836778 y x
       grind)
    | exact resolve eq16 eq836778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836778
  have eq839430 : (k y x) = (M.op y y) ∨ (k y x) = (M.op x x) := by
    first
    | (have j1 := eq749581 y x
       grind)
    | (have r₁ := eq838671
       have r₂ := eq749581 y x
       grind)
    | exact resolve eq838671 eq749581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749581 eq838671
  have eq841213 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq839430
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq839430
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq839430 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841220 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq289 y x
       have i₂ := eq839430
       grind)
    | exact superpose eq839430 eq289
    | (have j0 := eq289 y x
       grind)
    | exact resolve eq289 eq839430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq841223 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq949 y x
       have i₂ := eq839430
       grind)
    | exact superpose eq839430 eq949
    | (have j0 := eq949 y x
       grind)
    | (have r₁ := eq949 y x
       have r₂ := eq839430
       grind)
    | exact resolve eq949 eq839430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq841306 : (M.op x x) ≠ (M.op y y) ∨ (k y x) = (M.op x x) := by grind
  clear eq839430
  have eq841311 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (k y x) = (M.op x x) := by grind
  clear eq841223
  have eq841313 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (k y x) = (M.op x x) := by grind
  clear eq841220
  have eq841316 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq841213
  have eq841382 : (M.op x y) = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq841311
       have r₂ := eq841306
       grind)
    | exact resolve eq841311 eq841306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841311
  have eq842716 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq841316
       grind)
    | exact superpose eq841316 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq841316
       grind)
    | exact resolve eq13 eq841316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841316
  have eq842736 : (k y x) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq842716
  have eq849405 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (τ (k X1 X0)) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq834403 X1 X0
       grind)
    | exact superpose eq834403 eq11
    | (have j1 := eq834403 X1 X0
       grind)
    | exact resolve eq11 eq834403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834403
  have eq851418 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ (k X1 X0)) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq849405 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq849405
    | (have j0 := eq849405 X0 X1
       grind)
    | exact resolve eq849405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849405
  have eq853773 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ (k X0 X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq851418 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq851418
    | exact resolve eq851418 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855738 : (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (τ (k y x)) = (τ (M.op y y)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq842736
       have i₂ := eq851418 x y
       grind)
    | exact superpose eq851418 eq842736
    | (have j1 := eq851418 x y
       grind)
    | exact resolve eq842736 eq851418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851418
  have eq855745 : (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (τ (k y x)) = (τ (M.op y y)) ∨ (k y x) = (M.op x x) := by grind
  clear eq855738
  have eq855755 : (M.op x y) = (M.op y y) ∨ (τ (k y x)) = (τ (M.op y y)) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq855745
       have r₂ := eq841306
       grind)
    | exact resolve eq855745 eq841306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841306 eq855745
  have eq857399 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq853773 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq853773
    | (have j0 := eq853773 X0 X1
       grind)
    | exact resolve eq853773 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853773
  have eq857431 : (k y x) = (M.op x x) ∨ (τ (k y x)) = (τ (M.op y y)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq855755
       have r₂ := eq12 y x
       grind)
    | exact resolve eq855755 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855755
  have eq857894 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq857399 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq857399
    | (have j0 := eq857399 X0 X1
       grind)
    | exact resolve eq857399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857399
  have eq858177 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq857894 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq857894
    | (have j0 := eq857894 X0 X1
       grind)
    | exact resolve eq857894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857894
  have eq858319 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq858177 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq858177
    | (have j0 := eq858177 X0 X1
       grind)
    | exact resolve eq858177 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858177
  have eq858388 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (τ (M.op y y)) = (M.op (τ x) (τ y)) ∨ (τ (k y x)) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq5775 y x
       have i₂ := eq857431
       grind)
    | exact superpose eq857431 eq5775
    | (have j0 := eq5775 y x
       grind)
    | exact resolve eq5775 eq857431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5775 eq857431
  have eq858428 : (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (τ (M.op y y)) = (M.op (τ x) (τ y)) ∨ (τ (k y x)) = (τ (M.op y y)) := by grind
  clear eq858388
  have eq858436 : (τ (M.op y y)) = (M.op (τ x) (τ y)) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) := by
    first
    | (have j1 := eq5895 y x
       grind)
    | (have r₁ := eq858428
       have r₂ := eq5895 y x
       grind)
    | exact resolve eq858428 eq5895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5895 eq858428
  have eq859982 : (τ (k y x)) = (τ (M.op y y)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (k y x)) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq858436
       have i₂ := eq726701 y x
       grind)
    | exact superpose eq726701 eq858436
    | (have j1 := eq726701 y x
       grind)
    | exact resolve eq858436 eq726701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726701 eq858436
  have eq860076 : (τ (k y x)) = (τ (M.op y y)) ∨ (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq859982
  have eq860209 : (k y x) = (σ (τ (M.op y y))) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq860076
       grind)
    | exact superpose eq860076 eq11
    | exact resolve eq11 eq860076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861334 : (τ (M.op x x)) ≠ (τ (M.op y y)) ∨ (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq860076
  have eq862227 : (k y x) = (M.op y y) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq860209
       have i₂ := eq11 (M.op y y)
       grind)
    | exact superpose eq11 eq860209
    | exact resolve eq860209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860209
  have eq968406 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq858319 y x
       grind)
    | exact superpose eq858319 eq16
    | (have j1 := eq858319 y x
       grind)
    | exact resolve eq16 eq858319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858319
  have eq969263 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq968406
       have i₂ := eq554606 x y
       grind)
    | exact superpose eq554606 eq968406
    | (have j1 := eq554606 x y
       grind)
    | (have r₁ := eq968406
       have r₂ := eq554606 x y
       grind)
    | exact resolve eq968406 eq554606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554606 eq968406
  have eq969266 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq969263
  have eq969267 : (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq969266
  have eq972143 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq555012 x y
       have i₂ := eq969267
       grind)
    | exact superpose eq969267 eq555012
    | (have j0 := eq555012 x y
       grind)
    | exact resolve eq555012 eq969267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555012 eq969267
  have eq972162 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq972143
  have eq983932 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq841313
       grind)
    | exact superpose eq841313 eq16
    | exact resolve eq16 eq841313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841313
  have eq984117 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (k y x) = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq983932
       have i₂ := eq841382
       grind)
    | exact superpose eq841382 eq983932
    | exact resolve eq983932 eq841382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841382 eq983932
  have eq984132 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (k y x) = (M.op x x) := by grind
  clear eq984117
  have eq984133 : (k y x) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq984132
  have eq986933 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq984133
       have i₂ := eq862227
       grind)
    | exact superpose eq862227 eq984133
    | exact resolve eq984133 eq862227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862227 eq984133
  have eq1016117 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq861334
       have i₂ := eq986933
       grind)
    | exact superpose eq986933 eq861334
    | exact resolve eq861334 eq986933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986933
  have eq1016334 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq1016117
  have eq1016335 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq1016334
  have eq1018975 : (M.op y y) = (τ (σ (M.op x x))) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1016335
       grind)
    | exact superpose eq1016335 eq10
    | exact resolve eq10 eq1016335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016335
  have eq1019395 : (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq1018975
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1018975
    | exact resolve eq1018975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018975
  have eq1019412 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) ∨ (τ (M.op x x)) = (τ (k y x)) := by
    first
    | (have i₁ := eq861334
       have i₂ := eq1019395
       grind)
    | exact superpose eq1019395 eq861334
    | exact resolve eq861334 eq1019395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861334 eq1019395
  have eq1019629 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq1019412
  have eq1019630 : (τ (M.op x x)) = (τ (k y x)) := by grind
  clear eq1019629
  have eq1021679 : (k y x) = (σ (τ (M.op x x))) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq1019630
       grind)
    | exact superpose eq1019630 eq11
    | exact resolve eq11 eq1019630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019630
  have eq1023757 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq1021679
       have i₂ := eq11 (M.op x x)
       grind)
    | exact superpose eq11 eq1021679
    | exact resolve eq1021679 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021679
  have eq1023769 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq842736
       have i₂ := eq1023757
       grind)
    | exact superpose eq1023757 eq842736
    | exact resolve eq842736 eq1023757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842736
  have eq1023773 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq263 x y
       have i₂ := eq1023757
       grind)
    | exact superpose eq1023757 eq263
    | (have j0 := eq263 x y
       grind)
    | exact resolve eq263 eq1023757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq1023854 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1023773
  have eq1023856 : (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq1023769
  have eq1037747 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  have eq1046485 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1023854
       grind)
    | exact superpose eq1023854 eq16
    | exact resolve eq16 eq1023854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1046566 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1023854
  have eq1046682 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1046485
       have i₂ := eq1023856
       grind)
    | exact superpose eq1023856 eq1046485
    | exact resolve eq1046485 eq1023856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046485
  have eq1046701 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq1046682
  have eq1047746 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1046701
       grind)
    | exact superpose eq1046701 eq16
    | exact resolve eq16 eq1046701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047750 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq78 x (σ y)
       have i₂ := eq1046701
       grind)
    | exact superpose eq1046701 eq78
    | (have j0 := eq78 x (σ y)
       grind)
    | (have r₁ := eq78 x (σ y)
       have r₂ := eq1046701
       grind)
    | exact resolve eq78 eq1046701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1046701
  have eq1047830 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq1047750
  have eq1047860 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1047830
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1047830
    | exact resolve eq1047830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047830
  have eq1047882 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1047860
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq1047860
    | exact resolve eq1047860 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047860
  have eq1047894 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1047882
       have i₂ := eq1023757
       grind)
    | exact superpose eq1023757 eq1047882
    | exact resolve eq1047882 eq1023757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023757 eq1047882
  have eq1047902 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1047894
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq1047894
    | exact resolve eq1047894 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1047894
  have eq1047903 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq1047902
  have eq1049311 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1047903
       have i₂ := eq1023856
       grind)
    | exact superpose eq1023856 eq1047903
    | exact resolve eq1047903 eq1023856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023856 eq1047903
  have eq1049551 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq1049311
       have r₂ := eq1037747
       grind)
    | exact resolve eq1049311 eq1037747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037747 eq1049311
  have eq1049555 : (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq1049551
       have r₂ := eq1047746
       grind)
    | exact resolve eq1049551 eq1047746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047746 eq1049551
  have eq1049578 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq972162
       have i₂ := eq1049555
       grind)
    | exact superpose eq1049555 eq972162
    | exact resolve eq972162 eq1049555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972162
  have eq1049788 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq1049578
  have eq1057214 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1046566
       have i₂ := eq1049555
       grind)
    | exact superpose eq1049555 eq1046566
    | exact resolve eq1046566 eq1049555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046566 eq1049555
  have eq1057234 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1057214
  have eq1057736 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1057234
       grind)
    | exact superpose eq1057234 eq16
    | exact resolve eq16 eq1057234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057234
  have eq1057900 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1057736
       have i₂ := eq1049788
       grind)
    | exact superpose eq1049788 eq1057736
    | (have r₁ := eq1057736
       have r₂ := eq1049788
       grind)
    | exact resolve eq1057736 eq1049788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049788
  have eq1057913 : (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq1057900
  have eq1057926 : False := by grind
  exact eq1057926

/-- `Equation2646`: `x = ((x ◇ x) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation2646 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2646.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq84 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq144 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq890 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq144 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq144
    | (have j0 := eq144 (σ X0) (σ X1)
       grind)
    | exact resolve eq144 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq4654 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq84 (σ X1) X1
       grind)
    | (have r₁ := eq13 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq84 (M.op (M.op (σ X1) (σ X1)) X1) X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4682 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq4683 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4682 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq4685 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4654 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654
  have eq4686 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4685 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4685
  have eq4688 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4683 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4683
    | (have j0 := eq4683 X0
       grind)
    | exact resolve eq4683 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4683
  have eq4750 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq4688 X0
       grind)
    | exact superpose eq4688 eq38
    | (have j1 := eq4688 X0
       grind)
    | exact resolve eq38 eq4688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq4688
  have eq4779 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4750 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4750
    | (have j0 := eq4750 X0
       grind)
    | exact resolve eq4750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4750
  have eq4780 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4779 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779
  have eq4784 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4780 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4780
    | exact resolve eq4780 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4810 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4780 X0
       grind)
    | exact superpose eq4780 eq11
    | exact resolve eq11 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4780
  have eq4876 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4784 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq4784
    | exact resolve eq4784 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq4992 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4876 X0
       grind)
    | exact superpose eq4876 eq11
    | exact resolve eq11 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4876
  have eq5107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4992 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4992
    | exact resolve eq4992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4992
  have eq5850 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5887 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5850 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5850
    | exact resolve eq5850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5850
  have eq5936 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5887 X0
       have i₂ := eq5107 X0
       grind)
    | exact superpose eq5107 eq5887
    | exact resolve eq5887 eq5107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5887
  have eq5969 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5936
  have eq27632 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq890 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq890
    | (have j0 := eq890 (τ X0) (τ X1)
       grind)
    | exact resolve eq890 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq890
  have eq27712 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27632 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq27632
    | (have j0 := eq27632 X0 X1
       grind)
    | exact resolve eq27632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27632
  have eq27768 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27712 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27712
    | (have j0 := eq27712 X0 X1
       grind)
    | exact resolve eq27712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27712
  have eq27823 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27768 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27768
    | (have j0 := eq27768 X0 X1
       grind)
    | exact resolve eq27768 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27768
  have eq27873 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27823 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27823
    | (have j0 := eq27823 X0 X1
       grind)
    | exact resolve eq27823 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27823
  have eq27915 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27873 X0 X1
       have i₂ := eq4810 (σ (τ X1))
       grind)
    | exact superpose eq4810 eq27873
    | (have j0 := eq27873 X0 X1
       grind)
    | exact resolve eq27873 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27873
  have eq27955 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27915 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq27915
    | (have j0 := eq27915 X0 X1
       grind)
    | exact resolve eq27915 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27915
  have eq27992 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27955 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq27955
    | (have j0 := eq27955 X0 X1
       grind)
    | exact resolve eq27955 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq27955
  have eq28027 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27992 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27992
    | (have j0 := eq27992 X0 X1
       grind)
    | exact resolve eq27992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27992
  have eq28054 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28027 X0 X1
       have i₂ := eq5107 X1
       grind)
    | exact superpose eq5107 eq28027
    | (have j0 := eq28027 X0 X1
       grind)
    | exact resolve eq28027 eq5107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28027
  have eq28077 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28054 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28054
    | (have j0 := eq28054 X0 X1
       grind)
    | exact resolve eq28054 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28054
  have eq39595 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X1)
       have i₂ := eq4686 (σ X0) X1
       grind)
    | exact superpose eq4686 eq30
    | (have j1 := eq4686 (σ X0) X1
       grind)
    | exact resolve eq30 eq4686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4686
  have eq39705 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq39595 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq39595
    | (have j0 := eq39595 X0 X1
       grind)
    | exact resolve eq39595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39595
  have eq39809 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq39705 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39705
    | (have j0 := eq39705 X0 X1
       grind)
    | exact resolve eq39705 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39705
  have eq39908 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq39809 X0 X1
       have i₂ := eq4810 X1
       grind)
    | exact superpose eq4810 eq39809
    | (have j0 := eq39809 X0 X1
       grind)
    | exact resolve eq39809 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810 eq39809
  have eq39990 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq39908 X0 X1
       have i₂ := eq5107 X1
       grind)
    | exact superpose eq5107 eq39908
    | (have j0 := eq39908 X0 X1
       grind)
    | exact resolve eq39908 eq5107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5107 eq39908
  have eq40045 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39990 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39990
    | (have j0 := eq39990 X0 X1
       grind)
    | exact resolve eq39990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39990
  have eq42117 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq40045 X0 X1
       grind)
    | exact superpose eq40045 eq11
    | (have j1 := eq40045 X0 X1
       grind)
    | exact resolve eq11 eq40045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40045
  have eq43207 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42117 x y
       grind)
    | exact superpose eq42117 eq16
    | (have j1 := eq42117 x y
       grind)
    | exact resolve eq16 eq42117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42117
  have eq43730 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq43207
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq43207
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq43207 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43207
  have eq43733 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq43730
  have eq43734 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq43733
  have eq44265 : x ≠ x ∨ x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq43734
       grind)
    | exact superpose eq43734 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq43734
       grind)
    | exact resolve eq13 eq43734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44273 : x ≠ x ∨ x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq44265
  have eq44274 : x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq44273
  have eq44293 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq28077 x y
       have i₂ := eq44274
       grind)
    | exact superpose eq44274 eq28077
    | (have j0 := eq28077 x y
       grind)
    | exact resolve eq28077 eq44274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28077 eq44274
  have eq44298 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq44293
  have eq44299 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq44298
  have eq44847 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44299
       grind)
    | exact superpose eq44299 eq16
    | exact resolve eq16 eq44299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44299
  have eq44939 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44847
       have i₂ := eq43734
       grind)
    | exact superpose eq43734 eq44847
    | exact resolve eq44847 eq43734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43734 eq44847
  have eq44940 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq44939
  have eq44941 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq44940
  have eq45494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5969 y
       have i₂ := eq44941
       grind)
    | exact superpose eq44941 eq5969
    | exact resolve eq5969 eq44941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44941
  have eq45518 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq45494
       have r₂ := eq16
       grind)
    | exact resolve eq45494 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45494
  have eq45538 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq45518
       grind)
    | exact superpose eq45518 eq10
    | exact resolve eq10 eq45518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45518
  have eq45680 : x = (M.op y y) := by
    first
    | (have i₁ := eq45538
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq45538
    | exact resolve eq45538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45538
  have eq46344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5969 y
       have i₂ := eq45680
       grind)
    | exact superpose eq45680 eq5969
    | exact resolve eq5969 eq45680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5969 eq45680
  have eq46368 : False := by grind
  exact eq46368

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pxy_pxy_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  clear eq24 eq35
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq43
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq73 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq78 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
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
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq44
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq44 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq122
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq145 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq148 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq145
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq145
    | exact resolve eq145 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq150 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq148
       have i₂ := eq67 sF0
       grind)
    | exact superpose eq67 eq148
    | exact resolve eq148 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq148
  have eq171 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq150 eq16
    | exact resolve eq16 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq236 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq241 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq659 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq125 eq86
    | (have j0 := eq86 (σ x) (σ y)
       grind)
    | exact resolve eq86 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq786
    | exact resolve eq786 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq790 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq787
       have r₂ := eq27
       grind)
    | exact resolve eq787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq792 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq790
    | exact resolve eq790 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq794 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq792 eq79
    | (have r₁ := eq79
       have r₂ := eq792
       grind)
    | exact resolve eq79 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq792
  have eq809 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq794
  have eq956 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq809 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq809
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq809
       grind)
    | exact resolve eq13 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq963 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq956
       have r₂ := eq26
       grind)
    | exact resolve eq956 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq965 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq963
    | exact resolve eq963 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq125 eq965
    | exact resolve eq965 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq965 eq125
    | exact resolve eq125 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq965
  have eq1099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq1095
  have eq1100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1093
  have eq1101 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1099
       have r₂ := eq27
       grind)
    | exact resolve eq1099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1102 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1100
       have r₂ := eq27
       grind)
    | exact resolve eq1100 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1105 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1102
       grind)
    | exact superpose eq1102 eq73
    | exact resolve eq73 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1126 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq1105
    | exact resolve eq1105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1136 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) X0)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1126 eq14
    | exact resolve eq14 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (σ (M.op x y))) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1126 eq14
    | exact resolve eq14 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1175 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1126 eq659
    | exact resolve eq659 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1126 eq659
    | exact resolve eq659 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1300 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1101 eq59
    | exact resolve eq59 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1101
  have eq1306 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq1300
    | exact resolve eq1300 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1300
  have eq1327 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq1306
       grind)
    | exact superpose eq1306 eq78
    | (have r₁ := eq78
       have r₂ := eq1306
       grind)
    | exact resolve eq78 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1328 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1306
       grind)
    | exact superpose eq1306 eq73
    | exact resolve eq73 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1348 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq1327
  have eq1349 : (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq1348
  have eq1352 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq1328
    | exact resolve eq1328 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1386 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1349
       grind)
    | exact superpose eq1349 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1349
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1349
       grind)
    | exact resolve eq13 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1399 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq1386
       have r₂ := eq18
       grind)
    | exact resolve eq1386 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1401 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1399
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1399
    | exact resolve eq1399 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1481 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1401
       grind)
    | exact superpose eq1401 eq44
    | exact resolve eq44 eq1401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1484 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq1481
    | exact resolve eq1481 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481
  have eq1544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq1484 eq86
    | (have j0 := eq86 (σ x) (σ y)
       grind)
    | exact resolve eq86 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq1544
    | exact resolve eq1544 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1548 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq1545
       have r₂ := eq27
       grind)
    | exact resolve eq1545 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq1550 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq1548
    | exact resolve eq1548 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq1550 eq1352
    | exact resolve eq1352 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352 eq1550
  have eq1626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq1601
  have eq1631 : x = (k x y) := by
    first
    | (have r₁ := eq1626
       have r₂ := eq27
       grind)
    | exact resolve eq1626 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq1636 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1631
       grind)
    | exact superpose eq1631 eq44
    | exact resolve eq44 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1637 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq86 x y
       have i₂ := eq1631
       grind)
    | exact superpose eq1631 eq86
    | (have j0 := eq86 x y
       grind)
    | exact resolve eq86 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq1638 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1637
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1637
    | exact resolve eq1637 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq1639 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1636
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1636
    | exact resolve eq1636 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1641 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1638
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1638
    | exact resolve eq1638 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1638
  have eq1700 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1639 eq86
    | (have j0 := eq86 (σ x) (σ y)
       grind)
    | exact resolve eq86 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq1639
  have eq1701 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1700
    | exact resolve eq1700 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq1704 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1701
    | exact resolve eq1701 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701
  have eq1760 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1641
       grind)
    | exact superpose eq1641 eq73
    | exact resolve eq73 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1641
  have eq1783 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1760
    | exact resolve eq1760 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1760
  have eq1788 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1704 eq1126
    | exact resolve eq1126 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1813 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1788
       have r₂ := eq27
       grind)
    | exact resolve eq1788 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788
  have eq1870 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1813 eq241
    | exact resolve eq241 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq1945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1783 eq1704
    | exact resolve eq1704 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1968 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1945
       have r₂ := eq27
       grind)
    | exact resolve eq1945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq1971 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1968 eq27
    | exact resolve eq27 eq1968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968
  have eq2254 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1783 eq1870
    | exact resolve eq1870 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq2258 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1126 eq1870
    | exact resolve eq1870 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870
  have eq2274 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2258
  have eq2277 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2254
       have r₂ := eq1971
       grind)
    | exact resolve eq2254 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254
  have eq3916 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1126 eq1136
    | exact resolve eq1136 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq1136
  have eq3933 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3916
  have eq4037 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq1175
    | (have j0 := eq1175 (σ y)
       grind)
    | exact resolve eq1175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq4072 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) X0)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq4037 eq14
    | exact resolve eq14 eq4037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4037
  have eq4089 : (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4072 x
       have i₂ := eq659 sF1 sF2 x
       grind)
    | exact superpose eq659 eq4072
    | exact resolve eq4072 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4072
  have eq4184 : (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq1201
    | (have j0 := eq1201 (σ y)
       grind)
    | exact resolve eq1201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4193 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1201 eq1137
    | exact resolve eq1137 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq1201
  have eq4209 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq4193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193
  have eq4256 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1813 eq4184
    | exact resolve eq4184 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813 eq4184
  have eq4274 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4256
  have eq4303 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ (M.op x y)) X0) X1)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq4209 eq659
    | exact resolve eq659 eq4209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq4209
  have eq4310 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) X0) X1)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq4303 x X1
       have i₂ := eq14 sF1 x x
       grind)
    | exact superpose eq14 eq4303
    | exact resolve eq4303 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303
  have eq4895 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3933 eq4089
    | exact resolve eq4089 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3933 eq4089
  have eq4913 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4895
  have eq5202 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2274 eq4310
    | exact resolve eq4310 eq2274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4310
  have eq5272 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq5202 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5202
  have eq5304 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4913 eq5272
    | exact resolve eq5272 eq4913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4913 eq5272
  have eq5335 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5304
  have eq5350 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5335 eq4274
    | exact resolve eq4274 eq5335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274 eq5335
  have eq5385 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5350
  have eq5464 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5385 eq2277
    | exact resolve eq2277 eq5385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277
  have eq5465 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5385 eq2274
    | exact resolve eq2274 eq5385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274 eq5385
  have eq5485 : (σ (M.op x y)) = (σ x) := by grind
  clear eq5465
  have eq5486 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq5464
  have eq5489 : x = (M.op x y) := by
    first
    | (have r₁ := eq5486
       have r₂ := eq1971
       grind)
    | exact resolve eq5486 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971 eq5486
  have eq5548 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5485 eq1704
    | exact resolve eq1704 eq5485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704
  have eq5563 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq5548
       have r₂ := eq27
       grind)
    | exact resolve eq5548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5548
  have eq5587 : x = (M.op (M.op x x) y) := by
    first
    | exact superpose eq5489 eq236
    | exact resolve eq236 eq5489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq5855 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5563 eq171
    | exact resolve eq171 eq5563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq5563
  have eq5886 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5489 eq5855
    | exact resolve eq5855 eq5489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5489 eq5855
  have eq6473 : x = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | (have i₁ := eq5587
       have i₂ := eq5886
       grind)
    | exact superpose eq5886 eq5587
    | exact resolve eq5587 eq5886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5587
  have eq6478 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op x (M.op (τ (M.op (σ x) (σ y))) X0)) y) := by
    intro X0
    first
    | exact superpose eq6473 eq14
    | exact resolve eq14 eq6473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9560 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq6473 eq6478
    | exact resolve eq6478 eq6473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6478
  have eq9577 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | (have i₁ := eq9560
       have i₂ := eq5886
       grind)
    | exact superpose eq5886 eq9560
    | exact resolve eq9560 eq5886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5886 eq9560
  have eq9580 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6473 eq9577
    | exact resolve eq9577 eq6473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6473 eq9577
  have eq9941 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9580 eq15
    | exact resolve eq15 eq9580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9580
  have eq9986 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9941
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9941
    | exact resolve eq9941 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9941
  have eq10008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5485 eq9986
    | exact resolve eq9986 eq5485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5485 eq9986
  have eq10026 : False := by grind
  exact eq10026

/-- `Equation2676`: `x = ((x ◇ y) ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation2676 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2676 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2676.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq45
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq54 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X1 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 (M.op x x))) = (k (σ X0) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq10
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq92 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq88
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq22 eq100
    | exact resolve eq100 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq14
    | exact resolve eq14 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (σ X0) (σ X0) X2
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq56
    | exact resolve eq56 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X0 X1) X1 X2 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq524 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq525 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq56 X0 X1 x X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : ∀ X0 : G, (M.op (M.op (M.op X0 x) x) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq57 eq214
    | exact resolve eq214 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq214
  have eq891 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 x) (M.op x X1)) x) (M.op x y)) = (M.op X0 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq880 (M.op X0 (M.op x X2))
       have i₂ := eq56 X0 x X1 X2
       grind)
    | exact superpose eq56 eq880
    | exact resolve eq880 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq891 X0 x X2
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq891
    | exact resolve eq891 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq935 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq58 eq218
    | exact resolve eq218 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq946 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) X1)) (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq935 (M.op X0 (M.op sF2 x))
       have i₂ := eq56 X0 sF2 X2 x
       grind)
    | exact superpose eq56 eq935
    | exact resolve eq935 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq955 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq946 X0 X2 X2
       have i₂ := eq14 X0 sF2 X2
       grind)
    | exact superpose eq14 eq946
    | exact resolve eq946 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq994 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq521 (M.op (M.op X0 X1) X1) (M.op X1 X2) X3
       have i₂ := eq521 X0 X1 X2
       grind)
    | exact superpose eq521 eq521
    | exact resolve eq521 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X1) (M.op X1 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq521 (M.op X0 (M.op X1 X3)) X1 X4
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq521
    | exact resolve eq521 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1031 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ X0)) (σ X0)) (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq521 X1 (σ X0) (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq521
    | exact resolve eq521 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1058 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X3)) = (M.op X0 (M.op X1 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq996 X0 X1 x X3 X4
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq996
    | exact resolve eq996 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1076 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq524 eq525
    | exact resolve eq525 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq9583 : (σ (k (M.op x x) (M.op x x))) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq69 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq69
    | exact resolve eq69 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq69
  have eq9685 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (k (M.op x x) (M.op x x))) := by grind
  clear eq9583
  have eq9690 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by grind
  clear eq9685
  have eq9692 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq955 eq9690
    | exact resolve eq9690 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq9690
  have eq9693 : (σ (M.op (M.op x x) (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq9692
       have i₂ := eq900 (M.op x x) x
       grind)
    | exact superpose eq900 eq9692
    | exact resolve eq9692 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq9692
  have eq10382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq10383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq28 eq10382
    | exact resolve eq10382 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10382
  have eq10394 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq10383
       have r₂ := eq29
       grind)
    | exact resolve eq10383 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10383
  have eq10551 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq10394 eq126
    | exact resolve eq126 eq10394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq10394
  have eq10602 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq10551
    | exact resolve eq10551 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10551
  have eq10603 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10602
  have eq10622 : x = (M.op (M.op (M.op x y) y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq523 y
       have i₂ := eq10603
       grind)
    | exact superpose eq10603 eq523
    | exact resolve eq523 eq10603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq10627 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq425 y X0
       have i₂ := eq10603
       grind)
    | exact superpose eq10603 eq425
    | exact resolve eq425 eq10603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq10642 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq521 y y X0
       have i₂ := eq10603
       grind)
    | exact superpose eq10603 eq521
    | exact resolve eq521 eq10603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq10603
  have eq10650 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10642 X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq10642
    | (have j0 := eq10642 X0
       grind)
    | exact resolve eq10642 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10642
  have eq10654 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10627 x
       have i₂ := eq506 y (σ x) x
       grind)
    | exact superpose eq506 eq10627
    | exact resolve eq10627 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq10627
  have eq10666 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10654
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq10654
    | exact resolve eq10654 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq10654
  have eq10671 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10666
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10666
    | exact resolve eq10666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10666
  have eq10674 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10671
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10671
    | exact resolve eq10671 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10671
  have eq10675 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq10674
    | exact resolve eq10674 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10674
  have eq11224 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10622 eq880
    | exact resolve eq880 eq10622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq10622
  have eq11311 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) (M.op x y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f11311_13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) = X0 := by
      intro X0 X1 X2
      grind
    have f11311_14 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) ∨ (σ x) = (σ y) ∨ y = x := by
      intro X0
      grind
    have f11311_22 : X0 ≠ (M.op (M.op (M.op X0 y) (M.op x y)) (M.op x y)) := by grind
    have f11311_23 : (σ x) ≠ (σ y) := by grind
    have f11311_24 : y ≠ x := by grind
    have f11311_26 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) ∨ y = x := by
      intro X0
      first
      | (have j0 := f11311_14 X0
         grind)
      | (have r₁ := f11311_14 X0
         have r₂ := f11311_23
         grind)
      | exact resolve f11311_14 f11311_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11311_27 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
      intro X0
      first
      | (have j0 := f11311_26 X0
         grind)
      | (have r₁ := f11311_26 X0
         have r₂ := f11311_24
         grind)
      | exact resolve f11311_26 f11311_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11311_41 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) (M.op x y)) = X0 := by
      intro X0
      first
      | (have i₁ := f11311_13 X0 (M.op x y) (M.op y x)
         have i₂ := f11311_27 x
         grind)
      | exact superpose f11311_27 f11311_13
      | exact resolve f11311_13 f11311_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11311_134 : X0 ≠ X0 := by
      first
      | (have i₁ := f11311_22
         have i₂ := f11311_41 X0
         grind)
      | exact superpose f11311_41 f11311_22
      | (have r₁ := f11311_22
         have r₂ := f11311_41 X0
         grind)
      | exact resolve f11311_22 f11311_41
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11311_139 : False := by grind
    exact f11311_139
  clear eq525 eq10650
  have eq11758 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq10675 eq1058
    | exact resolve eq1058 eq10675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10675
  have eq19705 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11224 eq9693
    | exact resolve eq9693 eq11224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9693 eq11224
  have eq56292 : (σ x) = (M.op (σ (M.op (M.op x y) y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19705 eq58
    | exact resolve eq58 eq19705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq19705
  have eq78430 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11758 eq1076
    | exact resolve eq1076 eq11758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq11758
  have eq107132 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq56292 eq78430
    | exact resolve eq78430 eq56292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56292 eq78430
  have eq107291 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq107132
  have eq107345 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq107291
    | exact resolve eq107291 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107291
  have eq107389 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq107345
       have i₂ := eq1058 sF4 sF4 sF3 x
       grind)
    | (have i₁ := eq107345
       have i₂ := eq1058 sF4 sF4 x sF3
       grind)
    | exact superpose eq1058 eq107345
    | exact resolve eq107345 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058 eq107345
  have eq107617 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op (M.op x y) y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq107389 eq107389
    | exact resolve eq107389 eq107389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107389
  have eq107828 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op (M.op x y) y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq107617
  have eq476065 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq107828 eq1031
    | exact resolve eq1031 eq107828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq107828
  have eq476296 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))) (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq476065
       have i₂ := eq46 (M.op sF0 y)
       grind)
    | exact superpose eq46 eq476065
    | exact resolve eq476065 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476065
  have eq476338 : (M.op (σ x) (σ y)) = (σ (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq476296
       have i₂ := eq46 (M.op (M.op sF0 y) (M.op sF0 y))
       grind)
    | exact superpose eq46 eq476296
    | exact resolve eq476296 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq476296
  have eq476343 : (M.op (σ x) (σ y)) = (σ (M.op (M.op (M.op (M.op x y) y) (M.op x y)) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq476338
       have i₂ := eq994 (M.op sF0 y) sF0 y (M.op sF0 y)
       grind)
    | exact superpose eq994 eq476338
    | exact resolve eq476338 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994 eq476338
  have eq476349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11311 eq476343
    | exact resolve eq476343 eq11311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11311 eq476343
  have eq476499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq476349
  have eq476536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22 eq476499
    | exact resolve eq476499 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476499
  have eq476545 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq476536
       have r₂ := eq29
       grind)
    | exact resolve eq476536 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476536
  have eq476556 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq476545 eq31
    | exact resolve eq31 eq476545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq476545
  have eq476761 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq476556
    | exact resolve eq476556 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq476556
  have eq476762 : x = y := by grind
  clear eq476761
  have eq476798 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq476762
       grind)
    | exact superpose eq476762 eq20
    | exact resolve eq20 eq476762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq476799 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq476762
       grind)
    | exact superpose eq476762 eq26
    | exact resolve eq26 eq476762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq476762
  have eq477133 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq476799
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq476799
    | exact resolve eq476799 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq476799
  have eq477182 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq477133 eq28
    | exact resolve eq28 eq477133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq477133
  have eq477975 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq477182 eq71
    | exact resolve eq71 eq477182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq477182
  have eq478331 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq477975
       have i₂ := eq476798
       grind)
    | exact superpose eq476798 eq477975
    | exact resolve eq477975 eq476798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476798 eq477975
  have eq478462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq478331 eq15
    | exact resolve eq15 eq478331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478331
  have eq478785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq478462
    | exact resolve eq478462 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq478462
  have eq478887 : False := by grind
  exact eq478887

/-- `Equation2808`: `x = ((y ◇ z) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pyx_pxy_Equation2808 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2808 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2808.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X1)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq60 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 x
       grind)
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq95 : ∀ X0 X1 : G, (k (σ (σ X0)) X1) = (σ (σ (k X0 (τ (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (σ X0)
       have i₂ := eq48 (τ X1) X0
       grind)
    | exact superpose eq48 eq48
    | exact resolve eq48 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X0)) ≠ (M.op (M.op X0 X1) (M.op X1 X0)) ∨ (M.op X2 X2) = X2 ∨ (k (M.op (M.op X0 X1) (M.op X1 X0)) X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) (M.op X1 X0)) X2
       have i₂ := eq9 (M.op (M.op X0 X1) (M.op X1 X0)) X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) (M.op X1 X0)) X2
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X2) (M.op X2 X1)) X1
       have r₂ := eq9 (M.op (M.op X1 X2) (M.op X2 X1)) X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X1) (M.op X1 X0)) X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X0))) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq151 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq161 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq102
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq651 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq666 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq669 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq662
  have eq674 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq666
    | exact resolve eq666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq894 : ∀ X0 X1 X2 : G, (σ (σ (k (k X0 (τ X1)) (τ (τ X2))))) = (k (σ (k (σ X0) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 (k X0 (τ X1)) X2
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq95
    | exact resolve eq95 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 : G, (σ (k (σ X0) y)) = (σ (σ (k X0 (τ (τ (σ y)))))) := by
    intro X0
    first
    | (have i₁ := eq35 (σ X0)
       have i₂ := eq95 X0 sF3
       grind)
    | exact superpose eq95 eq35
    | exact resolve eq35 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq95
  have eq945 : ∀ X0 : G, (σ (k (σ X0) y)) = (σ (σ (k X0 (τ y)))) := by
    intro X0
    first
    | exact superpose eq39 eq930
    | exact resolve eq930 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq1869 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X1 X2) (M.op X2 X1))) X0) = (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X2 X1)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X0 (M.op (M.op X1 X2) (M.op X2 X1))
       have i₂ := eq160 X1 X2 (τ X0)
       grind)
    | exact superpose eq160 eq48
    | (have j1 := eq160 X0 X1 (τ X0)
       grind)
    | exact resolve eq48 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq160
  have eq4002 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq651 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq651
    | (have j0 := eq651 (σ X0) (σ X0)
       grind)
    | exact resolve eq651 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq9343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq674
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq674
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq674 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq9361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9343
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9343
    | exact resolve eq9343 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9343
  have eq9364 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq9361
    | exact resolve eq9361 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9361
  have eq9365 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq9364
       have r₂ := eq27
       grind)
    | exact resolve eq9364 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9364
  have eq9367 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq9365 eq9
    | exact resolve eq9 eq9365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9382 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq9365 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq9365
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq9365
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq9365
       grind)
    | exact resolve eq12 eq9365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9383 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq9382 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9382
  have eq9830 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq9365 eq9367
    | exact resolve eq9367 eq9365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9365 eq9367
  have eq9890 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq9830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9830
  have eq10024 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq9383 eq161
    | exact resolve eq161 eq9383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9383
  have eq10033 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39 eq10024
    | exact resolve eq10024 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10024
  have eq13199 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq9890 eq10033
    | exact resolve eq10033 eq9890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9890 eq10033
  have eq13233 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq13199
  have eq13249 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq39 eq13233
    | exact resolve eq13233 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13233
  have eq13270 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq13249
       grind)
    | exact superpose eq13249 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq13249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13249
  have eq13272 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq13270
  have eq13292 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq13272 eq9
    | exact resolve eq9 eq13272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13317 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq13272 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq13272
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq13272
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq13272
       grind)
    | exact resolve eq12 eq13272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13318 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq13317 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13317
  have eq13370 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq13272 eq13292
    | exact resolve eq13292 eq13272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13272 eq13292
  have eq13464 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq13370 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13370
  have eq14453 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq13318 eq161
    | exact resolve eq161 eq13318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13318
  have eq14466 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 X0)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq38 eq14453
    | exact resolve eq14453 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14453
  have eq46499 : ∀ X0 X1 : G, (σ (M.op x (M.op (M.op X0 X1) (M.op X1 X0)))) = (k (σ (M.op (M.op X0 X1) (M.op X1 X0))) (σ x)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq38 eq1869
    | exact resolve eq1869 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq47063 : ∀ X0 X1 : G, (σ (k (M.op (M.op X0 X1) (M.op X1 X0)) x)) = (σ (M.op x (M.op (M.op X0 X1) (M.op X1 X0)))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq30 eq46499
    | exact resolve eq46499 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq46499
  have eq126206 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq13464 eq14466
    | exact resolve eq14466 eq13464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13464 eq14466
  have eq126288 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq126206
  have eq126430 : x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq126288
    | exact resolve eq126288 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126288
  have eq126452 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq126430
       grind)
    | exact superpose eq126430 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq126430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126430
  have eq126469 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq126452
  have eq126540 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq126469
       grind)
    | exact superpose eq126469 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq126469
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq126469
       grind)
    | exact resolve eq12 eq126469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126547 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq126469
       grind)
    | exact superpose eq126469 eq9
    | exact resolve eq9 eq126469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126619 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq126540 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126540
  have eq126687 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq126547 X0
       have i₂ := eq126469
       grind)
    | exact superpose eq126469 eq126547
    | exact resolve eq126547 eq126469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126469 eq126547
  have eq127010 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq126687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126687
  have eq127947 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq161 X0 y
       have i₂ := eq126619 X0
       grind)
    | exact superpose eq126619 eq161
    | exact resolve eq161 eq126619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134269 : (τ y) = (k (τ y) (τ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq127947 y
       have i₂ := eq127010 y
       grind)
    | exact superpose eq127010 eq127947
    | exact resolve eq127947 eq127010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127010
  have eq134371 : (τ y) = (k (τ y) (τ y)) ∨ x = (M.op x x) := by grind
  clear eq134269
  have eq134562 : (σ (τ y)) = (k y (σ (τ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq49 y (τ y)
       have i₂ := eq134371
       grind)
    | exact superpose eq134371 eq49
    | exact resolve eq49 eq134371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134563 : (τ y) = (M.op (τ y) (τ y)) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14 (τ y) (τ y)
       have i₂ := eq134371
       grind)
    | exact superpose eq134371 eq14
    | (have j0 := eq14 (τ y) (τ y)
       grind)
    | exact resolve eq14 eq134371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134567 : (σ (σ (τ y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) ∨ (σ (σ (τ y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) ∨ (σ (σ (τ y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4002 (τ y) (τ y)
       have i₂ := eq134371
       grind)
    | exact superpose eq134371 eq4002
    | (have j0 := eq4002 (τ y) (τ y)
       grind)
    | exact resolve eq4002 eq134371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134371
  have eq134586 : (σ (σ (τ y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) ∨ x = (M.op x x) := by grind
  clear eq134567
  have eq134588 : (τ y) = (M.op (τ y) (τ y)) ∨ x = (M.op x x) := by grind
  clear eq134563
  have eq134614 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq134586
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq134586
    | exact resolve eq134586 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134586
  have eq134616 : y = (k y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq134562
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq134562
    | exact resolve eq134562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134562
  have eq134632 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq134614
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq134614
    | exact resolve eq134614 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134614
  have eq134724 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) ∨ (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) ∨ (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4002 y y
       have i₂ := eq134616
       grind)
    | exact superpose eq134616 eq4002
    | (have j0 := eq4002 y y
       grind)
    | exact resolve eq4002 eq134616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4002 eq134616
  have eq134735 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) ∨ x = (M.op x x) := by grind
  clear eq134724
  have eq134801 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq134735
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq134735
    | exact resolve eq134735 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134735
  have eq134854 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq134632 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq134632
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq134632
       grind)
    | exact resolve eq12 eq134632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134855 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq134632 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq134632
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq134632
       grind)
    | exact resolve eq13 eq134632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134863 : (τ (σ y)) = (k (τ (σ y)) (τ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq134632 eq127947
    | exact resolve eq127947 eq134632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134632
  have eq134932 : (τ (σ y)) = (k (τ (σ y)) (τ y)) ∨ x = (M.op x x) := by grind
  clear eq134863
  have eq134939 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq134855 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134855
  have eq134940 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq134854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134854
  have eq134972 : y = (k y (τ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39 eq134932
    | exact resolve eq134932 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134932
  have eq136372 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq134940 eq161
    | exact resolve eq161 eq134940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136615 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq39 eq136372
    | exact resolve eq136372 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq136372
  have eq138644 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (M.op X0 X0) = (k X0 (τ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (τ y)
       have i₂ := eq134588
       grind)
    | exact superpose eq134588 eq12
    | (have j0 := eq12 X0 (τ y)
       grind)
    | (have r₁ := eq12 X0 (τ y)
       have r₂ := eq134588
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq134588
       grind)
    | exact resolve eq12 eq134588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138652 : (τ (τ y)) = (k (τ (τ y)) (τ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq127947 (τ y)
       have i₂ := eq134588
       grind)
    | exact superpose eq134588 eq127947
    | exact resolve eq127947 eq134588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138654 : ∀ X0 : G, (M.op (M.op (τ y) (τ y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (τ y) (τ y)
       have i₂ := eq134588
       grind)
    | exact superpose eq134588 eq9
    | exact resolve eq9 eq134588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138683 : (τ (τ y)) = (k (τ (τ y)) (τ y)) ∨ x = (M.op x x) := by grind
  clear eq138652
  have eq138690 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq138644 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138644
  have eq138703 : ∀ X0 : G, (σ (σ y)) ≠ (σ (σ y)) ∨ (M.op X0 X0) = (k X0 (σ (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq134801 eq12
    | (have j0 := eq12 X0 (σ (σ y))
       grind)
    | (have r₁ := eq12 X0 (σ (σ y))
       have r₂ := eq134801
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq134801
       grind)
    | exact resolve eq12 eq134801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134801
  have eq138749 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq138703 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138703
  have eq139089 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (τ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq161 X0 (τ y)
       have i₂ := eq138690 X0
       grind)
    | exact superpose eq138690 eq161
    | exact resolve eq161 eq138690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138690
  have eq139506 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (σ (σ y)))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq138749 eq161
    | exact resolve eq161 eq138749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq138749
  have eq139580 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq139506 X0
       have i₂ := eq10 sF3
       grind)
    | exact superpose eq10 eq139506
    | exact resolve eq139506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139506
  have eq140639 : ∀ X0 : G, (M.op (τ y) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq138654 X0
       have i₂ := eq134588
       grind)
    | exact superpose eq134588 eq138654
    | exact resolve eq138654 eq134588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134588 eq138654
  have eq140841 : ∀ X0 : G, (M.op (τ y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq140639 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140639
  have eq143807 : (τ (τ y)) = (k (τ (τ y)) y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq136615 (τ y)
       have i₂ := eq140841 (τ y)
       grind)
    | exact superpose eq140841 eq136615
    | exact resolve eq136615 eq140841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136615 eq140841
  have eq143921 : (τ (τ y)) = (k (τ (τ y)) y) ∨ x = (M.op x x) := by grind
  clear eq143807
  have eq149873 : ∀ X0 : G, (k (τ X0) (τ y)) = (k (τ X0) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq127947 X0
       have i₂ := eq139580 X0
       grind)
    | exact superpose eq139580 eq127947
    | exact resolve eq127947 eq139580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127947 eq139580
  have eq149929 : ∀ X0 : G, (k (τ X0) (τ y)) = (k (τ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq149873 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149873
  have eq151123 : (τ (τ y)) = (M.op (τ (τ y)) (τ (τ y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq126619 (τ (τ y))
       have i₂ := eq143921
       grind)
    | exact superpose eq143921 eq126619
    | exact resolve eq126619 eq143921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126619 eq143921
  have eq151129 : (τ (τ y)) = (M.op (τ (τ y)) (τ (τ y))) ∨ x = (M.op x x) := by grind
  clear eq151123
  have eq160136 : ∀ X0 : G, (k (σ (k (σ (τ (τ y))) y)) X0) = (σ (σ (k (τ (τ y)) (τ (τ X0))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq894 (τ (τ y)) y X0
       have i₂ := eq138683
       grind)
    | exact superpose eq138683 eq894
    | exact resolve eq894 eq138683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq138683
  have eq160162 : ∀ X0 : G, (k (σ (k (σ (τ (τ y))) y)) X0) = (σ (k (τ y) (σ (τ (τ X0))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq160136 X0
       have i₂ := eq49 (τ y) (τ (τ X0))
       grind)
    | exact superpose eq49 eq160136
    | exact resolve eq160136 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160136
  have eq160169 : ∀ X0 : G, (k (σ (k (σ (τ (τ y))) y)) X0) = (k y (σ (σ (τ (τ X0))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq160162 X0
       have i₂ := eq49 y (σ (τ (τ X0)))
       grind)
    | exact superpose eq49 eq160162
    | exact resolve eq160162 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160162
  have eq160174 : ∀ X0 : G, (k y (σ (τ X0))) = (k (σ (k (σ (τ (τ y))) y)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq160169 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq160169
    | exact resolve eq160169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160169
  have eq160177 : ∀ X0 : G, (k y (σ (τ X0))) = (k (σ (σ (k (τ (τ y)) (τ y)))) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq160174 X0
       have i₂ := eq945 (τ (τ y))
       grind)
    | exact superpose eq945 eq160174
    | exact resolve eq160174 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq160174
  have eq160179 : ∀ X0 : G, (k y (σ (τ X0))) = (k (σ (k (τ y) (σ (τ y)))) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq160177 X0
       have i₂ := eq49 (τ y) (τ y)
       grind)
    | exact superpose eq49 eq160177
    | exact resolve eq160177 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160177
  have eq160181 : ∀ X0 : G, (k y (σ (τ X0))) = (k (k y (σ (σ (τ y)))) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq160179 X0
       have i₂ := eq49 y (σ (τ y))
       grind)
    | exact superpose eq49 eq160179
    | exact resolve eq160179 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq160179
  have eq160182 : ∀ X0 : G, (k y (σ (τ X0))) = (k (k y (σ y)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq160181 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq160181
    | exact resolve eq160181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160181
  have eq160183 : ∀ X0 : G, (k y (σ (τ X0))) = (k (k y (σ y)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq160182 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq160182
    | (have j0 := eq160182 X0
       grind)
    | exact resolve eq160182 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160182
  have eq160184 : ∀ X0 : G, (k y X0) = (k (k y (σ y)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq160183 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq160183
    | exact resolve eq160183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160183
  have eq171971 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (τ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq149929 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq149929
    | exact resolve eq149929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149929
  have eq172357 : (k y (τ y)) = (k (k y (σ y)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq160184 (τ y)
       have i₂ := eq171971 (k y sF3)
       grind)
    | exact superpose eq171971 eq160184
    | exact resolve eq160184 eq171971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160184 eq171971
  have eq172416 : (k y (τ y)) = (k (k y (σ y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq172357
  have eq181645 : y = (k (k y (σ y)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq134972
       have i₂ := eq172416
       grind)
    | exact superpose eq172416 eq134972
    | exact resolve eq134972 eq172416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134972 eq172416
  have eq181721 : y = (k (k y (σ y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq181645
  have eq181808 : y = (k (M.op y y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq134940 eq181721
    | exact resolve eq181721 eq134940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181721
  have eq181887 : y = (k (M.op y y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq181808
  have eq182031 : y = (M.op (M.op y y) (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq181887 eq134940
    | exact resolve eq134940 eq181887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134940 eq181887
  have eq182046 : y = (M.op (M.op y y) (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq182031
  have eq224567 : ∀ X0 : G, (τ (τ y)) ≠ (τ (τ y)) ∨ (M.op X0 X0) = (k X0 (τ (τ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (τ (τ y))
       have i₂ := eq151129
       grind)
    | exact superpose eq151129 eq12
    | (have j0 := eq12 X0 (τ (τ y))
       grind)
    | (have r₁ := eq12 X0 (τ (τ y))
       have r₂ := eq151129
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq151129
       grind)
    | exact resolve eq12 eq151129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151129
  have eq224579 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ (τ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq224567 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224567
  have eq224626 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq139089 X0
       have i₂ := eq224579 (τ X0)
       grind)
    | exact superpose eq224579 eq139089
    | exact resolve eq139089 eq224579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139089 eq224579
  have eq224659 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq224626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224626
  have eq334441 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq134939 eq61
    | (have j1 := eq134939 (σ x)
       grind)
    | exact resolve eq61 eq134939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq134939
  have eq334445 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq334441
    | exact resolve eq334441 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334441
  have eq385878 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq47063 y y
       have i₂ := eq182046
       grind)
    | exact superpose eq182046 eq47063
    | exact resolve eq47063 eq182046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47063 eq182046
  have eq385881 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) := by grind
  clear eq385878
  have eq385882 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq385881
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq385881
    | exact resolve eq385881 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385881
  have eq385883 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq385882
    | exact resolve eq385882 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385882
  have eq385887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq334445
       have i₂ := eq385883
       grind)
    | exact superpose eq385883 eq334445
    | exact resolve eq334445 eq385883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334445 eq385883
  have eq385910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq385887
  have eq385922 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq385910
       have r₂ := eq27
       grind)
    | exact resolve eq385910 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385910
  have eq385970 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq385922 eq224659
    | exact resolve eq224659 eq385922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224659 eq385922
  have eq385987 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by grind
  clear eq385970
  have eq386021 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq385987
    | exact resolve eq385987 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq385987
  have eq386022 : x = (M.op x x) := by grind
  clear eq386021
  have eq386124 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq386022
       grind)
    | exact superpose eq386022 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq386022
       grind)
    | exact resolve eq12 eq386022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386127 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq386022
       grind)
    | exact superpose eq386022 eq9
    | exact resolve eq9 eq386022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386259 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq386124 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386124
  have eq386390 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq386127 X0
       have i₂ := eq386022
       grind)
    | exact superpose eq386022 eq386127
    | exact resolve eq386127 eq386022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386022 eq386127
  have eq387419 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq669
       have i₂ := eq386259 x
       grind)
    | exact superpose eq386259 eq669
    | exact resolve eq669 eq386259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq386259
  have eq387596 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq386390 y
       grind)
    | exact superpose eq386390 eq18
    | (have j1 := eq386390 y
       grind)
    | exact resolve eq18 eq386390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq387625 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq387419
       have i₂ := eq386390 x
       grind)
    | exact superpose eq386390 eq387419
    | exact resolve eq387419 eq386390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386390 eq387419
  have eq388319 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq387596 eq20
    | exact resolve eq20 eq387596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq387596
  have eq391209 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq387625
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq387625
    | exact resolve eq387625 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq387625
  have eq391210 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq391209
  have eq391887 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq388319
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq388319
    | exact resolve eq388319 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq388319
  have eq391977 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq391887 eq26
    | exact resolve eq26 eq391887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq391887
  have eq396181 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq391210 eq9
    | exact resolve eq9 eq391210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396408 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq391210 eq396181
    | exact resolve eq396181 eq391210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391210 eq396181
  have eq396972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq396408 eq391977
    | exact resolve eq391977 eq396408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391977 eq396408
  have eq397651 : False := by grind
  exact eq397651

/-- `Equation2887`: `x = ((x ◇ (y ◇ z)) ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_pxx_pxy_Equation2887 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2887 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X3) X0)) (M.op X2 X3)) = (M.op (M.op X1 X2) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X1 (M.op (M.op X2 X3) X0)) (M.op X2 X3)) X2 X3
       have i₂ := eq9 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq55 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq55
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq124 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq124
    | (have j0 := eq124 (σ X0) (σ X1)
       grind)
    | exact resolve eq124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X3 X2) X2) (M.op X2 X1)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X2 X1) x
       have i₂ := eq30 x X3 X2 X1
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq211 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X2) = (M.op (M.op X1 X2) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq206 X3 X2 (M.op (M.op X1 (M.op X2 X0)) X2)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq206
    | exact resolve eq206 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq206 X0 X2 (M.op X1 (M.op X2 X3))
       have i₂ := eq9 X1 X2 X3
       grind)
    | exact superpose eq9 eq206
    | exact resolve eq206 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ X0)) (σ X0)) (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq206 (σ X0) (σ X0) X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq206
    | exact resolve eq206 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq125 x y
       grind)
    | exact superpose eq125 eq16
    | (have j1 := eq125 x y
       grind)
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq1173 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X2 X0) (M.op X0 X3)) X0) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq211 X3 (M.op X2 X0) X0 x
       have i₂ := eq206 x X0 X2
       grind)
    | exact superpose eq206 eq211
    | exact resolve eq211 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq1307 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1173 (σ X0) X1 (σ X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq1173
    | exact resolve eq1173 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1362 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq407
       have i₂ := eq124 x y
       grind)
    | exact superpose eq124 eq407
    | (have j1 := eq124 (σ x) (σ y)
       grind)
    | exact resolve eq407 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq407
  have eq1365 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1362
  have eq1369 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ (M.op y y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq226 y (σ x)
       have i₂ := eq1365
       grind)
    | exact superpose eq1365 eq226
    | exact resolve eq226 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq1365
  have eq1392 : (σ x) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1369
       have i₂ := eq59 y
       grind)
    | exact superpose eq59 eq1369
    | exact resolve eq1369 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1395 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1392
       have i₂ := eq59 (M.op y y)
       grind)
    | exact superpose eq59 eq1392
    | exact resolve eq1392 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1404 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1307 X0 (σ X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq1307
    | exact resolve eq1307 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq1444 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1404 X0
       have i₂ := eq59 (M.op X0 X0)
       grind)
    | exact superpose eq59 eq1404
    | exact resolve eq1404 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1404
  have eq1606 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (M.op (M.op X1 X1) (M.op X1 X0))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1444 X1
       have i₂ := eq218 X1 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq1444 X1
       have i₂ := eq218 X0 (M.op X1 X1) X1 X1
       grind)
    | exact superpose eq218 eq1444
    | exact resolve eq1444 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq1444
  have eq8414 : (M.op (M.op y y) (M.op y y)) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op (M.op y y) (M.op y y))
       have i₂ := eq1395
       grind)
    | exact superpose eq1395 eq10
    | exact resolve eq10 eq1395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq8466 : x = (M.op (M.op y y) (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8414
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8414
    | exact resolve eq8414 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8414
  have eq8471 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1173 y y y
       have i₂ := eq8466
       grind)
    | exact superpose eq8466 eq1173
    | exact resolve eq1173 eq8466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173 eq8466
  have eq8526 : y = (M.op x y) := by grind
  clear eq8471
  have eq8548 : ∀ X0 : G, x = (M.op (M.op y y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq206 X0 y x
       have i₂ := eq8526
       grind)
    | exact superpose eq8526 eq206
    | exact resolve eq206 eq8526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq9521 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1606 x y
       have i₂ := eq8548 x
       grind)
    | exact superpose eq8548 eq1606
    | exact resolve eq1606 eq8548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606 eq8548
  have eq9652 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9521
       grind)
    | exact superpose eq9521 eq16
    | exact resolve eq16 eq9521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9521
  have eq9709 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq9652
       have i₂ := eq8526
       grind)
    | exact superpose eq8526 eq9652
    | exact resolve eq9652 eq8526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8526 eq9652
  have eq9710 : False := by grind
  exact eq9710
