import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_y_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq35 (M.op X0 X1)
       grind)
    | exact superpose eq35 eq9
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq35 (σ X1)
       grind)
    | exact superpose eq35 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq91 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq97 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq35 (σ X1)
       grind)
    | exact superpose eq35 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq122 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq134 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq131 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq131 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq131 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq136 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq122
    | (have j0 := eq122 X0 X1
       grind)
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq134
    | (have j0 := eq134 X0 X1
       grind)
    | exact resolve eq134 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq138 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq35 (σ X1)
       grind)
    | exact superpose eq35 eq137
    | (have j0 := eq137 X0 X1
       grind)
    | exact resolve eq137 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq139 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq549 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136
    | exact resolve eq136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq693 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq139 (τ X1) (τ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq139
    | (have j0 := eq139 (τ X1) (τ (k X0 X1))
       grind)
    | exact resolve eq139 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq693
    | (have j0 := eq693 X0 X1
       grind)
    | exact resolve eq693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq709 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq704
    | (have j0 := eq704 X0 X1
       grind)
    | exact resolve eq704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq710 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq709 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq709
    | (have j0 := eq709 X0 X1
       grind)
    | exact resolve eq709 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq711 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq710
    | (have j0 := eq710 X0 X1
       grind)
    | exact resolve eq710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq712 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq711 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq711
    | (have j0 := eq711 X0 X1
       grind)
    | exact resolve eq711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq713 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq712
    | (have j0 := eq712 X0 X1
       grind)
    | exact resolve eq712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq722 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq713 (τ X1) (τ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq713
    | (have j0 := eq713 (τ X1) (τ (k X0 X1))
       grind)
    | exact resolve eq713 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq1178 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq87 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1193 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1178 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1198 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1193 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq1193
    | (have j0 := eq1193 X0 X1
       grind)
    | exact resolve eq1193 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1199 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1213 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (k (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op X0 (σ X1))
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq25
    | (have j1 := eq101 X0 X1
       grind)
    | exact resolve eq25 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1219 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k (σ (k (τ X0) X1)) (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1213 X0 X1
       have i₂ := eq35 (k (τ X0) X1)
       grind)
    | exact superpose eq35 eq1213
    | (have j0 := eq1213 X0 X1
       grind)
    | exact resolve eq1213 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1223 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1219 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1219
    | (have j0 := eq1219 X0 X1
       grind)
    | exact resolve eq1219 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq3382 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1199 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1199
    | exact resolve eq1199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq3445 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3382 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3382
    | (have j0 := eq3382 X0 X1
       grind)
    | exact resolve eq3382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq3598 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3445 X0 X1
       grind)
    | exact superpose eq3445 eq10
    | (have j1 := eq3445 X0 X1
       grind)
    | exact resolve eq10 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445
  have eq3656 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3598 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3598
    | (have j0 := eq3598 X0 X1
       grind)
    | exact resolve eq3598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3598
  have eq3662 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3656 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3656
    | (have j0 := eq3656 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq3656 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3707 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq3656 (σ X0) X1
       grind)
    | exact superpose eq3656 eq30
    | (have j1 := eq3656 (σ X0) X1
       grind)
    | exact resolve eq30 eq3656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3656
  have eq6672 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq3707 X1 (σ X0)
       grind)
    | exact superpose eq3707 eq23
    | (have j1 := eq3707 X1 (σ X0)
       grind)
    | exact resolve eq23 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3707
  have eq6741 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6672 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6672
    | (have j0 := eq6672 X0 X1
       grind)
    | exact resolve eq6672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6672
  have eq6775 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6741 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6741
    | (have j0 := eq6741 X0 X1
       grind)
    | exact resolve eq6741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6741
  have eq6782 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6775 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6775
    | (have j0 := eq6775 X0 X1
       grind)
    | exact resolve eq6775 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6775
  have eq7298 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6782 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6782
    | (have j0 := eq6782 X1 (τ X0)
       grind)
    | exact resolve eq6782 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6782
  have eq7516 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq7298 X0 X1
       grind)
    | exact superpose eq7298 eq11
    | (have j1 := eq7298 X0 X1
       grind)
    | exact resolve eq11 eq7298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7298
  have eq7595 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7516 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq7516
    | (have j0 := eq7516 X0 X1
       grind)
    | exact resolve eq7516 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7516
  have eq7616 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7595 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7595
    | (have j0 := eq7595 X1 (τ X0)
       grind)
    | exact resolve eq7595 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7595
  have eq7731 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7616 X0 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq7616
    | (have j0 := eq7616 X0 X1
       grind)
    | exact resolve eq7616 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq7616
  have eq7833 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (k X1 X0)
       have i₂ := eq7731 X0 X1
       grind)
    | exact superpose eq7731 eq25
    | (have j1 := eq7731 X0 X1
       grind)
    | exact resolve eq25 eq7731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq7731
  have eq7948 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7833 X0 X1
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq7833
    | (have j0 := eq7833 X0 X1
       grind)
    | exact resolve eq7833 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7833
  have eq7964 : ∀ X0 X1 : G, (k X0 (k X1 X0)) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7948 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7948
    | (have j0 := eq7948 X0 X1
       grind)
    | exact resolve eq7948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7948
  have eq8011 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 (k X1 X0)
       have i₂ := eq7964 X0 X1
       grind)
    | exact superpose eq7964 eq139
    | (have j0 := eq139 X1 X0
       have j1 := eq7964 X0 X1
       grind)
    | (have r₁ := eq139 X0 X1
       have r₂ := eq7964 (σ X0) (σ (k X0 X1))
       grind)
    | (have r₁ := eq139 X0 X1
       have r₂ := eq7964 (σ (k X0 X1)) (σ X0)
       grind)
    | exact resolve eq139 eq7964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq7964
  have eq8097 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8011 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8011
  have eq8098 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8097 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8097
  have eq8255 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq8098 (τ X0) X1
       grind)
    | exact superpose eq8098 eq19
    | (have j1 := eq8098 (τ X0) X1
       grind)
    | exact resolve eq19 eq8098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8098
  have eq8359 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (k (σ X1) X0) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8255 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8255
    | (have j0 := eq8255 X0 X1
       grind)
    | exact resolve eq8255 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8255
  have eq9308 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq8359 X1 X0
       grind)
    | exact superpose eq8359 eq19
    | (have j1 := eq8359 X1 X0
       grind)
    | exact resolve eq19 eq8359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8359
  have eq12823 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9308 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9308
    | (have j0 := eq9308 X1 (σ X0)
       grind)
    | exact resolve eq9308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9308
  have eq12935 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12823 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12823
    | (have j0 := eq12823 X0 X1
       grind)
    | exact resolve eq12823 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12823
  have eq12939 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12935 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12935
    | (have j0 := eq12935 X0 X1
       grind)
    | exact resolve eq12935 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12935
  have eq13153 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12939 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52069 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3662 x y
       grind)
    | exact superpose eq3662 eq16
    | (have j1 := eq3662 x y
       grind)
    | exact resolve eq16 eq3662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq52322 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq52069
       have i₂ := eq12939 y x
       grind)
    | exact superpose eq12939 eq52069
    | (have j1 := eq12939 y x
       grind)
    | (have r₁ := eq52069
       have r₂ := eq12939 y x
       grind)
    | (have r₁ := eq52069
       have r₂ := eq12939 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq52069
       have r₂ := eq12939 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq52069 eq12939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12939 eq52069
  have eq52327 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by grind
  clear eq52322
  have eq52332 : x = y ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq13153 x y
       grind)
    | (have r₁ := eq52327
       have r₂ := eq13153 x y
       grind)
    | exact resolve eq52327 eq13153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13153 eq52327
  have eq52598 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52332
       grind)
    | exact superpose eq52332 eq16
    | exact resolve eq16 eq52332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52332
  have eq52599 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52598
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq52598
    | exact resolve eq52598 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52598
  have eq52600 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52599
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq52599
    | exact resolve eq52599 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52599
  have eq52601 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq52600
  have eq52603 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq52601
       grind)
    | exact superpose eq52601 eq10
    | exact resolve eq10 eq52601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52601
  have eq52737 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq52603
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52603
    | exact resolve eq52603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52603
  have eq52955 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52737
       grind)
    | exact superpose eq52737 eq16
    | exact resolve eq16 eq52737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52737
  have eq52956 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq52955
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq52955
    | exact resolve eq52955 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52955
  have eq52957 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq52956
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq52956
    | exact resolve eq52956 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52956
  have eq52958 : (σ y) = (σ (k x y)) := by grind
  clear eq52957
  have eq52992 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq52958
       grind)
    | exact superpose eq52958 eq10
    | exact resolve eq10 eq52958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53128 : y = (k x y) := by
    first
    | (have i₁ := eq52992
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq52992
    | exact resolve eq52992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52992
  have eq53283 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq549 y x
       have i₂ := eq53128
       grind)
    | exact superpose eq53128 eq549
    | (have j0 := eq549 x y
       grind)
    | exact resolve eq549 eq53128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq53128
  have eq56004 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53283
       grind)
    | exact superpose eq53283 eq16
    | exact resolve eq16 eq53283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53283
  have eq56011 : (σ x) ≠ (σ (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56004
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq56004
    | exact resolve eq56004 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56004
  have eq56012 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56011
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq56011
    | exact resolve eq56011 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56011
  have eq56013 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq56012
  have eq56324 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq39 x y
       have i₂ := eq56013
       grind)
    | exact superpose eq56013 eq39
    | exact resolve eq39 eq56013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56364 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq56799 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56324
       have i₂ := eq56013
       grind)
    | exact superpose eq56013 eq56324
    | exact resolve eq56324 eq56013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56013 eq56324
  have eq56844 : x = y ∨ x = (M.op x y) := by grind
  clear eq56799
  have eq56851 : x = (M.op x y) := by
    first
    | (have r₁ := eq56844
       have r₂ := eq56364
       grind)
    | exact resolve eq56844 eq56364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56364 eq56844
  have eq99984 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1223 (σ x) y
       grind)
    | exact superpose eq1223 eq16
    | (have j1 := eq1223 (σ y) x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1223 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq100092 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq99984
       have i₂ := eq56851
       grind)
    | exact superpose eq56851 eq99984
    | exact resolve eq99984 eq56851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99984
  have eq100093 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq100092
  have eq100117 : (σ (k x y)) = (k (σ (k x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100093
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq100093
    | exact resolve eq100093 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100093
  have eq100130 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100117
       have i₂ := eq52958
       grind)
    | exact superpose eq52958 eq100117
    | exact resolve eq100117 eq52958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52958 eq100117
  have eq100204 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq722 (σ y) (M.op (σ x) (σ y))
       have i₂ := eq100130
       grind)
    | exact superpose eq100130 eq722
    | (have j0 := eq722 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq722 eq100130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq100130
  have eq100341 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq100204
  have eq100342 : (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq100341
  have eq100414 : (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq100342
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq100342
    | exact resolve eq100342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100342
  have eq101283 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100414
       grind)
    | exact superpose eq100414 eq16
    | exact resolve eq16 eq100414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100414
  have eq101489 : (σ (M.op x y)) ≠ (σ x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq101283
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq101283
    | exact resolve eq101283 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq101283
  have eq101490 : (σ x) ≠ (σ x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq101489
       have i₂ := eq56851
       grind)
    | exact superpose eq56851 eq101489
    | exact resolve eq101489 eq56851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101489
  have eq101491 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq101490
  have eq101570 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq101491
       grind)
    | exact superpose eq101491 eq11
    | exact resolve eq11 eq101491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101491
  have eq102211 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101570
       grind)
    | exact superpose eq101570 eq16
    | exact resolve eq16 eq101570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102271 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq39 (σ x) (σ y)
       have i₂ := eq101570
       grind)
    | exact superpose eq101570 eq39
    | exact resolve eq39 eq101570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq102407 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102271
       have i₂ := eq101570
       grind)
    | exact superpose eq101570 eq102271
    | exact resolve eq102271 eq101570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102271
  have eq102430 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq102211
       have i₂ := eq56851
       grind)
    | exact superpose eq56851 eq102211
    | exact resolve eq102211 eq56851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56851 eq102211
  have eq103066 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq101570
       have i₂ := eq102407
       grind)
    | exact superpose eq102407 eq101570
    | exact resolve eq101570 eq102407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101570 eq102407
  have eq103180 : False := by grind
  exact eq103180

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_x_pyy_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq35 (M.op X0 X1)
       grind)
    | exact superpose eq35 eq9
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq35 (σ X1)
       grind)
    | exact superpose eq35 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq94 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq100 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq35 (σ X1)
       grind)
    | exact superpose eq35 eq100
    | (have j0 := eq100 X0 X1
       grind)
    | exact resolve eq100 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq125 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq137 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq134 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq134 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq134 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq139 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq125
    | (have j0 := eq125 X0 X1
       grind)
    | exact resolve eq125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq140 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq35 (σ X1)
       grind)
    | exact superpose eq35 eq137
    | (have j0 := eq137 X0 X1
       grind)
    | exact resolve eq137 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq141 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq140
    | (have j0 := eq140 X0 X1
       grind)
    | exact resolve eq140 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq142 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq35 (σ X1)
       grind)
    | exact superpose eq35 eq141
    | (have j0 := eq141 X0 X1
       grind)
    | exact resolve eq141 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq143 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq554 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq139
    | exact resolve eq139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq698 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 (τ X1) (τ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq143
    | (have j0 := eq143 (τ X1) (τ (k X0 X1))
       grind)
    | exact resolve eq143 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq698
    | (have j0 := eq698 X0 X1
       grind)
    | exact resolve eq698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq714 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq709 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq709
    | (have j0 := eq709 X0 X1
       grind)
    | exact resolve eq709 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq715 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq714 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq714
    | (have j0 := eq714 X0 X1
       grind)
    | exact resolve eq714 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq716 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq715
    | (have j0 := eq715 X0 X1
       grind)
    | exact resolve eq715 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq717 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq718 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq717 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq717
    | (have j0 := eq717 X0 X1
       grind)
    | exact resolve eq717 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq727 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq718 (τ X1) (τ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq718
    | (have j0 := eq718 (τ X1) (τ (k X0 X1))
       grind)
    | exact resolve eq718 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq1184 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq90 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq1199 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1204 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1199 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq1199
    | (have j0 := eq1199 X0 X1
       grind)
    | exact resolve eq1199 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1209 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1204 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq1204
    | (have j0 := eq1204 X0 X1
       grind)
    | exact resolve eq1204 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1210 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1209 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1220 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (k (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op X0 (σ X1))
       have i₂ := eq104 X0 X1
       grind)
    | exact superpose eq104 eq25
    | (have j1 := eq104 X0 X1
       grind)
    | exact resolve eq25 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq1226 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k (σ (k (τ X0) X1)) (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1220 X0 X1
       have i₂ := eq35 (k (τ X0) X1)
       grind)
    | exact superpose eq35 eq1220
    | (have j0 := eq1220 X0 X1
       grind)
    | exact resolve eq1220 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1230 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1226 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1226
    | (have j0 := eq1226 X0 X1
       grind)
    | exact resolve eq1226 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq3395 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1210 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1210
    | exact resolve eq1210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq3458 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3395 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3395
    | (have j0 := eq3395 X0 X1
       grind)
    | exact resolve eq3395 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3395
  have eq3612 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3458 X0 X1
       grind)
    | exact superpose eq3458 eq10
    | (have j1 := eq3458 X0 X1
       grind)
    | exact resolve eq10 eq3458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458
  have eq3670 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3612 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3612
    | (have j0 := eq3612 X0 X1
       grind)
    | exact resolve eq3612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3612
  have eq3676 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3670 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3670
    | (have j0 := eq3670 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq3670 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3721 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq3670 (σ X0) X1
       grind)
    | exact superpose eq3670 eq30
    | (have j1 := eq3670 (σ X0) X1
       grind)
    | exact resolve eq30 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3670
  have eq6698 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq3721 X1 (σ X0)
       grind)
    | exact superpose eq3721 eq23
    | (have j1 := eq3721 X1 (σ X0)
       grind)
    | exact resolve eq23 eq3721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3721
  have eq6767 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6698 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6698
    | (have j0 := eq6698 X0 X1
       grind)
    | exact resolve eq6698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6698
  have eq6801 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6767 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6767
    | (have j0 := eq6767 X0 X1
       grind)
    | exact resolve eq6767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6767
  have eq6808 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6801 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6801
    | (have j0 := eq6801 X0 X1
       grind)
    | exact resolve eq6801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801
  have eq7326 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6808 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6808
    | (have j0 := eq6808 X1 (τ X0)
       grind)
    | exact resolve eq6808 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6808
  have eq7545 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq7326 X0 X1
       grind)
    | exact superpose eq7326 eq11
    | (have j1 := eq7326 X0 X1
       grind)
    | exact resolve eq11 eq7326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7326
  have eq7624 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7545 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq7545
    | (have j0 := eq7545 X0 X1
       grind)
    | exact resolve eq7545 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7545
  have eq7645 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7624 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7624
    | (have j0 := eq7624 X1 (τ X0)
       grind)
    | exact resolve eq7624 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7624
  have eq7760 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7645 X0 X1
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq7645
    | (have j0 := eq7645 X0 X1
       grind)
    | exact resolve eq7645 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq7645
  have eq7863 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (k X1 X0)
       have i₂ := eq7760 X0 X1
       grind)
    | exact superpose eq7760 eq25
    | (have j1 := eq7760 X0 X1
       grind)
    | exact resolve eq25 eq7760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq7760
  have eq7978 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7863 X0 X1
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq7863
    | (have j0 := eq7863 X0 X1
       grind)
    | exact resolve eq7863 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7863
  have eq7994 : ∀ X0 X1 : G, (k X0 (k X1 X0)) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7978 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7978
    | (have j0 := eq7978 X0 X1
       grind)
    | exact resolve eq7978 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7978
  have eq8041 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 (k X1 X0)
       have i₂ := eq7994 X0 X1
       grind)
    | exact superpose eq7994 eq143
    | (have j0 := eq143 X1 X0
       have j1 := eq7994 X0 X1
       grind)
    | (have r₁ := eq143 X0 X1
       have r₂ := eq7994 (σ X0) (σ (k X0 X1))
       grind)
    | (have r₁ := eq143 X0 X1
       have r₂ := eq7994 (σ (k X0 X1)) (σ X0)
       grind)
    | exact resolve eq143 eq7994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq7994
  have eq8127 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8041 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8041
  have eq8128 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8127
  have eq8285 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq8128 (τ X0) X1
       grind)
    | exact superpose eq8128 eq19
    | (have j1 := eq8128 (τ X0) X1
       grind)
    | exact resolve eq19 eq8128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8128
  have eq8389 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (k (σ X1) X0) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8285 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8285
    | (have j0 := eq8285 X0 X1
       grind)
    | exact resolve eq8285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8285
  have eq9341 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq8389 X1 X0
       grind)
    | exact superpose eq8389 eq19
    | (have j1 := eq8389 X1 X0
       grind)
    | exact resolve eq19 eq8389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8389
  have eq12886 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9341 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9341
    | (have j0 := eq9341 X1 (σ X0)
       grind)
    | exact resolve eq9341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9341
  have eq12998 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12886 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12886
    | (have j0 := eq12886 X0 X1
       grind)
    | exact resolve eq12886 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12886
  have eq13002 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12998 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12998
    | (have j0 := eq12998 X0 X1
       grind)
    | exact resolve eq12998 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12998
  have eq13217 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13002 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52184 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3676 x y
       grind)
    | exact superpose eq3676 eq16
    | (have j1 := eq3676 x y
       grind)
    | exact resolve eq16 eq3676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3676
  have eq52437 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq52184
       have i₂ := eq13002 y x
       grind)
    | exact superpose eq13002 eq52184
    | (have j1 := eq13002 y x
       grind)
    | (have r₁ := eq52184
       have r₂ := eq13002 y x
       grind)
    | (have r₁ := eq52184
       have r₂ := eq13002 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq52184
       have r₂ := eq13002 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq52184 eq13002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13002 eq52184
  have eq52442 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by grind
  clear eq52437
  have eq52447 : x = y ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq13217 x y
       grind)
    | (have r₁ := eq52442
       have r₂ := eq13217 x y
       grind)
    | exact resolve eq52442 eq13217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13217 eq52442
  have eq52714 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52447
       grind)
    | exact superpose eq52447 eq16
    | exact resolve eq16 eq52447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52447
  have eq52715 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52714
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq52714
    | exact resolve eq52714 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52714
  have eq52716 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52715
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq52715
    | exact resolve eq52715 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52715
  have eq52717 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq52716
  have eq52719 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq52717
       grind)
    | exact superpose eq52717 eq10
    | exact resolve eq10 eq52717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52717
  have eq52853 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq52719
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52719
    | exact resolve eq52719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52719
  have eq53072 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52853
       grind)
    | exact superpose eq52853 eq16
    | exact resolve eq16 eq52853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52853
  have eq53073 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq53072
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq53072
    | exact resolve eq53072 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53072
  have eq53074 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq53073
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq53073
    | exact resolve eq53073 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53073
  have eq53075 : (σ y) = (σ (k x y)) := by grind
  clear eq53074
  have eq53109 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq53075
       grind)
    | exact superpose eq53075 eq10
    | exact resolve eq10 eq53075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53245 : y = (k x y) := by
    first
    | (have i₁ := eq53109
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq53109
    | exact resolve eq53109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53109
  have eq53401 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq554 y x
       have i₂ := eq53245
       grind)
    | exact superpose eq53245 eq554
    | (have j0 := eq554 x y
       grind)
    | exact resolve eq554 eq53245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq53245
  have eq56124 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53401
       grind)
    | exact superpose eq53401 eq16
    | exact resolve eq16 eq53401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53401
  have eq56131 : (σ x) ≠ (σ (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56124
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq56124
    | exact resolve eq56124 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56124
  have eq56132 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56131
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq56131
    | exact resolve eq56131 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56131
  have eq56133 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq56132
  have eq56445 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq39 x y
       have i₂ := eq56133
       grind)
    | exact superpose eq56133 eq39
    | exact resolve eq39 eq56133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56485 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq56923 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56445
       have i₂ := eq56133
       grind)
    | exact superpose eq56133 eq56445
    | exact resolve eq56445 eq56133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56133 eq56445
  have eq56968 : x = y ∨ x = (M.op x y) := by grind
  clear eq56923
  have eq56976 : x = (M.op x y) := by
    first
    | (have r₁ := eq56968
       have r₂ := eq56485
       grind)
    | exact resolve eq56968 eq56485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56485 eq56968
  have eq100200 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1230 (σ x) y
       grind)
    | exact superpose eq1230 eq16
    | (have j1 := eq1230 (σ y) x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1230 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq100308 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq100200
       have i₂ := eq56976
       grind)
    | exact superpose eq56976 eq100200
    | exact resolve eq100200 eq56976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100200
  have eq100309 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq100308
  have eq100334 : (σ (k x y)) = (k (σ (k x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100309
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq100309
    | exact resolve eq100309 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100309
  have eq100347 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100334
       have i₂ := eq53075
       grind)
    | exact superpose eq53075 eq100334
    | exact resolve eq100334 eq53075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53075 eq100334
  have eq100421 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq727 (σ y) (M.op (σ x) (σ y))
       have i₂ := eq100347
       grind)
    | exact superpose eq100347 eq727
    | (have j0 := eq727 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq727 eq100347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq100347
  have eq100558 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq100421
  have eq100559 : (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq100558
  have eq100631 : (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq100559
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq100559
    | exact resolve eq100559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100559
  have eq101500 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100631
       grind)
    | exact superpose eq100631 eq16
    | exact resolve eq16 eq100631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100631
  have eq101706 : (σ (M.op x y)) ≠ (σ x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq101500
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq101500
    | exact resolve eq101500 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq101500
  have eq101707 : (σ x) ≠ (σ x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq101706
       have i₂ := eq56976
       grind)
    | exact superpose eq56976 eq101706
    | exact resolve eq101706 eq56976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101706
  have eq101708 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq101707
  have eq101787 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq101708
       grind)
    | exact superpose eq101708 eq11
    | exact resolve eq11 eq101708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101708
  have eq102429 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101787
       grind)
    | exact superpose eq101787 eq16
    | exact resolve eq16 eq101787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102489 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq39 (σ x) (σ y)
       have i₂ := eq101787
       grind)
    | exact superpose eq101787 eq39
    | exact resolve eq39 eq101787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq102625 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102489
       have i₂ := eq101787
       grind)
    | exact superpose eq101787 eq102489
    | exact resolve eq102489 eq101787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102489
  have eq102648 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq102429
       have i₂ := eq56976
       grind)
    | exact superpose eq56976 eq102429
    | exact resolve eq102429 eq56976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56976 eq102429
  have eq103286 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq101787
       have i₂ := eq102625
       grind)
    | exact superpose eq102625 eq101787
    | exact resolve eq101787 eq102625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101787 eq102625
  have eq103400 : False := by grind
  exact eq103400

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxy_pxx_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq15
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq95
    | exact resolve eq95 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq95
  have eq248 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106 x y
       grind)
    | exact superpose eq106 eq16
    | (have r₁ := eq16
       have r₂ := eq106 x y
       grind)
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq256 : False := by grind
  exact eq256

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq110 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq110
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq110 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 : G, X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq534 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq533 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq578 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq534 X1 (τ X0)
       grind)
    | exact superpose eq534 eq19
    | (have j1 := eq534 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq581 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq534 (σ X1) (σ X0)
       grind)
    | exact superpose eq534 eq15
    | (have j1 := eq534 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq663 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq578 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq578
    | exact resolve eq578 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq705 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq663
    | (have j0 := eq663 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq663 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq871 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq581 x y
       grind)
    | exact superpose eq581 eq16
    | (have j1 := eq581 x y
       grind)
    | exact resolve eq16 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq893 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq871
       have i₂ := eq705 x y
       grind)
    | exact superpose eq705 eq871
    | (have j1 := eq705 (σ x) (σ y)
       grind)
    | (have r₁ := eq871
       have r₂ := eq705 x y
       grind)
    | (have r₁ := eq871
       have r₂ := eq705 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq871
       have r₂ := eq705 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq871 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq871
  have eq894 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq893
  have eq896 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq894
       grind)
    | exact superpose eq894 eq16
    | exact resolve eq16 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq897 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq896
       have r₂ := eq22 x
       grind)
    | exact resolve eq896 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq896
  have eq898 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq897
       grind)
    | exact superpose eq897 eq16
    | exact resolve eq16 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq897
       grind)
    | exact superpose eq897 eq10
    | exact resolve eq10 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq938 : x = y := by
    first
    | (have i₁ := eq899
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq899
    | exact resolve eq899 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq939 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq898
       have i₂ := eq110 (σ x)
       grind)
    | exact superpose eq110 eq898
    | exact resolve eq898 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq941 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq939
       have i₂ := eq938
       grind)
    | exact superpose eq938 eq939
    | exact resolve eq939 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938 eq939
  have eq942 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq941
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq941
    | exact resolve eq941 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq941
  have eq943 : False := by grind
  exact eq943

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pxy_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq26 (M.op X0 X1)
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq32
    | (have j0 := eq32 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq32
    | (have j0 := eq32 (σ X0) (σ X1)
       grind)
    | exact resolve eq32 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51
    | exact resolve eq51 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq675 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq83 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq83 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq83 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq693 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq675
  have eq732 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (M.op (σ (σ X0)) (σ (σ (k X0 X1))))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ (σ X0)) (σ (σ X1))
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq34
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq34 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq810 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq693
       grind)
    | exact superpose eq693 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq693
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq693
       grind)
    | exact resolve eq13 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq818 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq810
  have eq819 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq818
  have eq822 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq819
       have i₂ := eq26 (σ y)
       grind)
    | exact superpose eq26 eq819
    | exact resolve eq819 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq824 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq822
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq822
    | exact resolve eq822 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq4167 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq824
       grind)
    | exact superpose eq824 eq10
    | exact resolve eq10 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq4200 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4167
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4167
    | exact resolve eq4167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4167
  have eq6446 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq4200
       grind)
    | exact superpose eq4200 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq4200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4200
  have eq6456 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6446
  have eq8760 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34 x y
       have i₂ := eq6456
       grind)
    | exact superpose eq6456 eq34
    | exact resolve eq34 eq6456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq13434 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (M.op (σ (σ (τ X0))) (σ (σ (τ (k X0 X1)))))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq732 (τ X0) (τ X1)
       have i₂ := eq156 X1 X0
       grind)
    | exact superpose eq156 eq732
    | (have j0 := eq732 (τ X0) (τ X1)
       grind)
    | exact resolve eq732 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq732
  have eq13550 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (M.op (σ (σ (τ X0))) (σ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13434 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq13434
    | (have j0 := eq13434 X0 X1
       grind)
    | exact resolve eq13434 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13434
  have eq13600 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13550 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13550
    | (have j0 := eq13550 X0 X1
       grind)
    | exact resolve eq13550 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13550
  have eq13632 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13600 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq13600
    | (have j0 := eq13600 X0 X1
       grind)
    | exact resolve eq13600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13600
  have eq13654 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13632 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13632
    | (have j0 := eq13632 X0 X1
       grind)
    | exact resolve eq13632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13632
  have eq13670 : ∀ X0 X1 : G, (σ X1) = (σ (σ (τ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13654 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq13654
    | (have j0 := eq13654 X0 X1
       grind)
    | exact resolve eq13654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13654
  have eq13683 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13670 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13670
    | (have j0 := eq13670 X0 X1
       grind)
    | exact resolve eq13670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13670
  have eq16256 : x = (M.op x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8760
       have i₂ := eq6456
       grind)
    | exact superpose eq6456 eq8760
    | exact resolve eq8760 eq6456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6456 eq8760
  have eq16286 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16256
  have eq21173 : x ≠ x ∨ x = y ∨ (k x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq16286
       grind)
    | exact superpose eq16286 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16286
       grind)
    | exact resolve eq13 eq16286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21189 : x ≠ x ∨ x = y ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq21173
  have eq21190 : x = y ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq21189
  have eq21196 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq21190
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq21190
    | exact resolve eq21190 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq21190
  have eq26344 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32 x y
       have i₂ := eq21196
       grind)
    | exact superpose eq21196 eq32
    | (have j0 := eq32 x y
       grind)
    | exact resolve eq32 eq21196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq26391 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26344
  have eq178844 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13683 x y
       have i₂ := eq21196
       grind)
    | exact superpose eq21196 eq13683
    | (have j0 := eq13683 x y
       grind)
    | exact resolve eq13683 eq21196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13683 eq21196
  have eq179003 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq178844
  have eq434151 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq179003
       have i₂ := eq26391
       grind)
    | exact superpose eq26391 eq179003
    | exact resolve eq179003 eq26391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26391 eq179003
  have eq434271 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq434151
  have eq458958 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq434271
       grind)
    | exact superpose eq434271 eq16
    | exact resolve eq16 eq434271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434271
  have eq478578 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq458958
       have i₂ := eq16286
       grind)
    | exact superpose eq16286 eq458958
    | exact resolve eq458958 eq16286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16286 eq458958
  have eq478583 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq478578
  have eq478584 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq478583
  have eq503540 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq478584
       grind)
    | exact superpose eq478584 eq10
    | exact resolve eq10 eq478584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478584
  have eq504507 : x = y ∨ x = y := by
    first
    | (have i₁ := eq503540
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq503540
    | exact resolve eq503540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503540
  have eq504508 : x = y := by grind
  clear eq504507
  have eq526353 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq504508
       grind)
    | exact superpose eq504508 eq16
    | exact resolve eq16 eq504508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504508
  have eq526354 : False := by grind
  exact eq526354

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq611 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq580
    | (have j0 := eq580 X0 X1
       grind)
    | exact resolve eq580 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq828 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq611 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq611
    | exact resolve eq611 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq611 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq858 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq828
    | (have j0 := eq828 X0 X1
       grind)
    | exact resolve eq828 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq828
  have eq875 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq858 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq858
    | exact resolve eq858 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq163 X0 (σ X1)
       have i₂ := eq858 X0 X1
       grind)
    | exact superpose eq858 eq163
    | (have j0 := eq163 (σ X1) X0
       have j1 := eq858 X0 X1
       grind)
    | (have r₁ := eq163 X0 (σ X1)
       have r₂ := eq858 X0 X1
       grind)
    | (have r₁ := eq163 (σ X1) X1
       have r₂ := eq858 (M.op (σ X1) X1) X1
       grind)
    | exact resolve eq163 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq858
  have eq894 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq887 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq895 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq894 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq951 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq895 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq895
    | exact resolve eq895 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq895 X0 X1
       grind)
    | exact superpose eq895 eq37
    | (have j1 := eq895 X0 X1
       grind)
    | exact resolve eq37 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq895
  have eq1025 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq951 (τ X1) X0
       grind)
    | exact superpose eq951 eq18
    | (have j1 := eq951 (τ X1) X0
       grind)
    | exact resolve eq18 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq951
  have eq5281 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq964 (σ X0) X1
       grind)
    | exact superpose eq964 eq28
    | (have j1 := eq964 (σ X0) X1
       grind)
    | exact resolve eq28 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq964
  have eq5343 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5281 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5281
    | (have j0 := eq5281 X0 X1
       grind)
    | exact resolve eq5281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5281
  have eq5381 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5343 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5343
    | (have j0 := eq5343 X0 X1
       grind)
    | exact resolve eq5343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5343
  have eq5394 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5381 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5381
    | (have j0 := eq5381 X0 X1
       grind)
    | exact resolve eq5381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5381
  have eq5406 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1025 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1025
    | exact resolve eq1025 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq5469 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5406 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5406
    | (have j0 := eq5406 X0 X1
       grind)
    | exact resolve eq5406 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5406
  have eq5721 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq5394 X1 X0
       grind)
    | exact superpose eq5394 eq11
    | (have j1 := eq5394 X1 X0
       grind)
    | exact resolve eq11 eq5394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5394
  have eq6828 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5721 y x
       grind)
    | exact superpose eq5721 eq16
    | (have j1 := eq5721 y x
       grind)
    | exact resolve eq16 eq5721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5721
  have eq6912 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6828
       have i₂ := eq875 y x
       grind)
    | exact superpose eq875 eq6828
    | (have j1 := eq875 y x
       grind)
    | (have r₁ := eq6828
       have r₂ := eq875 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6828
       have r₂ := eq875 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6828 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq6914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq6828
       have i₂ := eq5469 y x
       grind)
    | exact superpose eq5469 eq6828
    | (have j1 := eq5469 y x
       grind)
    | (have r₁ := eq6828
       have r₂ := eq5469 y x
       grind)
    | (have r₁ := eq6828
       have r₂ := eq5469 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6828
       have r₂ := eq5469 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6828 eq5469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5469 eq6828
  have eq6917 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6914
  have eq6918 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq6917
  have eq6920 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6912
  have eq6921 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6920
  have eq6927 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6918
       grind)
    | exact superpose eq6918 eq16
    | exact resolve eq16 eq6918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6918
  have eq6928 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6927
       have r₂ := eq22 x
       grind)
    | exact resolve eq6927 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6927
  have eq6933 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq849 x y
       have i₂ := eq6928
       grind)
    | exact superpose eq6928 eq849
    | (have j0 := eq849 x y
       grind)
    | exact resolve eq849 eq6928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq6928
  have eq6941 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6933
  have eq6942 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6941
  have eq6945 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6921
       grind)
    | exact superpose eq6921 eq16
    | exact resolve eq16 eq6921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6921
  have eq6946 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6945
       have r₂ := eq22 x
       grind)
    | exact resolve eq6945 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6945
  have eq6996 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6942
       grind)
    | exact superpose eq6942 eq16
    | exact resolve eq16 eq6942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6942
  have eq7035 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6996
       have i₂ := eq6946
       grind)
    | exact superpose eq6946 eq6996
    | exact resolve eq6996 eq6946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6946 eq6996
  have eq7038 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq7035
  have eq7039 : (σ x) = (σ y) := by grind
  clear eq7038
  have eq7040 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7039
       grind)
    | exact superpose eq7039 eq16
    | exact resolve eq16 eq7039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7041 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7039
       grind)
    | exact superpose eq7039 eq10
    | exact resolve eq10 eq7039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7039
  have eq7094 : x = y := by
    first
    | (have i₁ := eq7041
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7041
    | exact resolve eq7041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7041
  have eq7095 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq7040
       have i₂ := eq110 (σ x)
       grind)
    | exact superpose eq110 eq7040
    | exact resolve eq7040 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7040
  have eq7099 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7095
       have i₂ := eq7094
       grind)
    | exact superpose eq7094 eq7095
    | exact resolve eq7095 eq7094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7094 eq7095
  have eq7102 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq7099
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq7099
    | exact resolve eq7099 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq7099
  have eq7103 : False := by grind
  exact eq7103

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyx_pyy_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq110 X0
       grind)
    | exact resolve eq13 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq165 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq161 (τ X0) X1
       grind)
    | exact superpose eq161 eq19
    | (have j1 := eq161 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq166 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq161 (σ X0) (σ X1)
       grind)
    | exact superpose eq161 eq15
    | (have j1 := eq161 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq222 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq165 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq165
    | exact resolve eq165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq248 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq222
    | (have j0 := eq222 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq222 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq813 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq166 x y
       grind)
    | exact superpose eq166 eq16
    | (have j1 := eq166 x y
       grind)
    | exact resolve eq16 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq835 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq813
       have i₂ := eq248 x y
       grind)
    | exact superpose eq248 eq813
    | (have j1 := eq248 (σ x) (σ y)
       grind)
    | (have r₁ := eq813
       have r₂ := eq248 x y
       grind)
    | (have r₁ := eq813
       have r₂ := eq248 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq813
       have r₂ := eq248 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq813 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq813
  have eq836 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq835
  have eq838 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq836
       grind)
    | exact superpose eq836 eq16
    | exact resolve eq16 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq839 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq838
       have r₂ := eq22 x
       grind)
    | exact resolve eq838 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq838
  have eq840 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq839
       grind)
    | exact superpose eq839 eq16
    | exact resolve eq16 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq839
       grind)
    | exact superpose eq839 eq10
    | exact resolve eq10 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq880 : x = y := by
    first
    | (have i₁ := eq841
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq841
    | exact resolve eq841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq881 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq840
       have i₂ := eq110 (σ x)
       grind)
    | exact superpose eq110 eq840
    | exact resolve eq840 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq883 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq881
       have i₂ := eq880
       grind)
    | exact superpose eq880 eq881
    | exact resolve eq881 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq881
  have eq884 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq883
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq883
    | exact resolve eq883 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq883
  have eq885 : False := by grind
  exact eq885

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_pxx_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | exact resolve eq59 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq88 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq190 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq171
    | (have j0 := eq171 X0 X1
       grind)
    | exact resolve eq171 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq171
  have eq195 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       have j1 := eq88 X1 X0
       grind)
    | (have r₁ := eq190 X1 X0
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq190 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq190 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq190
  have eq199 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq195
    | exact resolve eq195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq195 (σ X0) X1
       grind)
    | exact superpose eq195 eq15
    | (have j1 := eq195 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq219 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq199 (τ X1) X0
       grind)
    | exact superpose eq199 eq18
    | (have j1 := eq199 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq199
  have eq319 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq219
    | exact resolve eq219 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq345 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq319 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq319
    | (have j0 := eq319 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq319 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq869 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq205 x y
       grind)
    | exact superpose eq205 eq16
    | (have j1 := eq205 x y
       grind)
    | exact resolve eq16 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq891 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq869
       have i₂ := eq345 y x
       grind)
    | exact superpose eq345 eq869
    | (have j1 := eq345 (σ x) (σ y)
       grind)
    | (have r₁ := eq869
       have r₂ := eq345 y x
       grind)
    | (have r₁ := eq869
       have r₂ := eq345 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq869
       have r₂ := eq345 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq869 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq869
  have eq892 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq891
  have eq951 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq892
       grind)
    | exact superpose eq892 eq10
    | exact resolve eq10 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq993 : x = y ∨ x = y := by
    first
    | (have i₁ := eq951
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq951
    | exact resolve eq951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq994 : x = y := by grind
  clear eq993
  have eq996 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq994
       grind)
    | exact superpose eq994 eq16
    | exact resolve eq16 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq997 : False := by grind
  exact eq997
