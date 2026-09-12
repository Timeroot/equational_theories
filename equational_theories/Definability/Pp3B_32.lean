import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq68 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (τ X0)) (M.op X1 X2))
       have i₂ := eq64 (τ X0) X1 X2
       grind)
    | exact superpose eq64 eq17
    | exact resolve eq17 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq69 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq107 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq107 (M.op X0 X1)
       grind)
    | exact superpose eq107 eq61
    | exact resolve eq61 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq9
    | exact resolve eq9 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq12
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq107 X0
       grind)
    | exact resolve eq12 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq61
    | exact resolve eq61 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq126 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op (M.op X0 X0) (τ X1)) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X1 (M.op X0 X0) X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq69
    | exact resolve eq69 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq130 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq121 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq132 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq130 (τ X0)
       grind)
    | exact superpose eq130 eq17
    | exact resolve eq17 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq133 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq132 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq132
    | exact resolve eq132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq142 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 (M.op X0 X1))
       have i₂ := eq118 X0 X1
       grind)
    | exact superpose eq118 eq12
    | (have r₁ := eq12 X1 (M.op X1 (M.op X0 X1))
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq12 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq151 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq206 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq120
    | exact resolve eq120 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq206 X0 X1
       grind)
    | exact superpose eq206 eq12
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq206 X0 X1
       grind)
    | exact resolve eq12 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq323 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op (M.op X1 X1) (τ (τ X0))) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op (M.op X1 X1) (τ (τ X0))) X1))
       have i₂ := eq126 X1 (τ X0)
       grind)
    | exact superpose eq126 eq17
    | exact resolve eq17 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq324 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op (M.op X1 X1) (τ (τ X0))) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq323
    | exact resolve eq323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq570 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq570
    | (have j0 := eq570 (σ X0) (σ X1)
       grind)
    | exact resolve eq570 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq570
    | (have j0 := eq570 (τ X0) (τ X1)
       grind)
    | exact resolve eq570 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq570 (τ X1) X0
       grind)
    | exact superpose eq570 eq17
    | (have j1 := eq570 (τ X1) X0
       grind)
    | exact resolve eq17 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1521 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq123
    | exact resolve eq123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1696 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X1 X0
       have i₂ := eq570 X1 X0
       grind)
    | exact superpose eq570 eq590
    | (have j0 := eq590 X1 X0
       have j1 := eq570 (σ X1) (σ X0)
       grind)
    | exact resolve eq590 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq2252 : ∀ X0 : G, (k X0 (k X0 (σ (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq618 (τ X0) X0
       grind)
    | exact superpose eq618 eq133
    | (have j1 := eq618 (τ X0) X0
       grind)
    | exact resolve eq133 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq618
  have eq2272 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2252 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2252
    | (have j0 := eq2252 X0
       grind)
    | exact resolve eq2252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252
  have eq2789 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) X1)))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (τ X0) X1
       have i₂ := eq2272 X0
       grind)
    | exact superpose eq2272 eq69
    | (have j1 := eq2272 X0
       grind)
    | exact resolve eq69 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq2793 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ X0)) X1) = X1 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq120 (τ X0) X1
       have i₂ := eq2272 X0
       grind)
    | exact superpose eq2272 eq120
    | (have j1 := eq2272 X0
       grind)
    | exact resolve eq120 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2838 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) (M.op (τ X0) X1)) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1521 (τ X0) (τ X0) x
       have i₂ := eq2272 X0
       grind)
    | exact superpose eq2272 eq1521
    | (have j1 := eq2272 X0
       grind)
    | exact resolve eq1521 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq2846 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2838 X0 X1
       have i₂ := eq206 (τ X0) X1
       grind)
    | exact superpose eq206 eq2838
    | (have j0 := eq2838 X0 X1
       grind)
    | exact resolve eq2838 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2838
  have eq2863 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2789 X0 X1
       have i₂ := eq206 (τ X0) X1
       grind)
    | exact superpose eq206 eq2789
    | (have j0 := eq2789 X0 X1
       grind)
    | exact resolve eq2789 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789
  have eq3432 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) ∨ (σ X0) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ (M.op (τ (σ X0)) X1))
       have i₂ := eq2863 (σ X0) X1
       grind)
    | exact superpose eq2863 eq28
    | (have j1 := eq2863 (σ X0) X1
       grind)
    | exact resolve eq28 eq2863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq3448 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) X1)) ∨ (σ X0) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3432 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq3432
    | (have j0 := eq3432 X0 X1
       grind)
    | exact resolve eq3432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432
  have eq3459 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (σ X0) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3448 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3448
    | (have j0 := eq3448 X0 X1
       grind)
    | exact resolve eq3448 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3448
  have eq3468 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3459 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3459
    | (have j0 := eq3459 X0 X1
       grind)
    | exact resolve eq3459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3459
  have eq3472 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3468 X0 X1
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq3468
    | (have j0 := eq3468 X0 X1
       grind)
    | exact resolve eq3468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq3759 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (k X0 X0)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq3472 X0 X1
       grind)
    | exact superpose eq3472 eq10
    | (have j1 := eq3472 X0 X1
       grind)
    | exact resolve eq10 eq3472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472
  have eq3789 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3759 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3759
    | (have j0 := eq3759 X0 X1
       grind)
    | exact resolve eq3759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3759
  have eq8290 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq592 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq8386 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8290 X0 (M.op X0 X1)
       have i₂ := eq245 X0 X1
       grind)
    | exact superpose eq245 eq8290
    | (have j0 := eq8290 X0 (M.op X0 X1)
       grind)
    | exact resolve eq8290 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq8290
  have eq9420 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq2846 eq2793
    | (have j0 := eq2793 X0 X1
       have j1 := eq2846 X0 X1
       grind)
    | exact resolve eq2793 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793 eq2846
  have eq9439 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (M.op (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (k (σ X0) (σ X0))
       have i₂ := eq9420 (σ X0) X1
       grind)
    | exact superpose eq9420 eq28
    | (have j1 := eq9420 (σ X0) X1
       grind)
    | exact resolve eq28 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9420
  have eq9458 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (k (τ (σ X0)) X0)) ∨ (M.op (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9439 X0 X1
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq9439
    | (have j0 := eq9439 X0 X1
       grind)
    | exact resolve eq9439 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9439
  have eq9472 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9458 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9458
    | (have j0 := eq9458 X0 X1
       grind)
    | exact resolve eq9458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9458
  have eq9478 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9472 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9472
    | (have j0 := eq9472 X0 X1
       grind)
    | exact resolve eq9472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9472
  have eq9479 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq9478 eq3789
    | (have j0 := eq3789 X0 X1
       have j1 := eq9478 X0 X1
       grind)
    | exact resolve eq3789 eq9478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789 eq9478
  have eq9559 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq9479 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9479
  have eq9560 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq9559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9559
  have eq9596 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9560 X0
       have i₂ := eq570 X0 (k X0 X0)
       grind)
    | exact superpose eq570 eq9560
    | (have j1 := eq570 X0 (k X0 X0)
       grind)
    | exact resolve eq9560 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq9655 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (k X0 X0)
       have i₂ := eq9596 X0
       grind)
    | exact superpose eq9596 eq13
    | (have j0 := eq13 X0 (k X0 X0)
       have j1 := eq9596 X0
       grind)
    | (have r₁ := eq13 X0 (k X0 X0)
       have r₂ := eq9596 X0
       grind)
    | exact resolve eq13 eq9596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9692 : ∀ X0 : G, (k X0 (M.op X0 (k X0 X0))) = X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq151 X0 (k X0 X0)
       have i₂ := eq9596 X0
       grind)
    | exact superpose eq9596 eq151
    | (have j1 := eq9596 X0
       grind)
    | exact resolve eq151 eq9596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq9738 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9596 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9596
  have eq9741 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9655 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9655
  have eq9778 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9741 X0
       have i₂ := eq9560 X0
       grind)
    | exact superpose eq9560 eq9741
    | (have j0 := eq9741 X0
       grind)
    | exact resolve eq9741 eq9560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9560 eq9741
  have eq9795 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq9778 X0
       have j1 := eq9738 X0
       grind)
    | (have r₁ := eq9778 X0
       have r₂ := eq9738 X0
       grind)
    | exact resolve eq9778 eq9738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9778
  have eq9952 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq9795 eq9692
    | (have j0 := eq9692 X0
       have j1 := eq9795 X0
       grind)
    | exact resolve eq9692 eq9795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9692 eq9795
  have eq9953 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9952 X0
       have j1 := eq9738 X0
       grind)
    | (have r₁ := eq9952 X0
       have r₂ := eq9738 X0
       grind)
    | exact resolve eq9952 eq9738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9738 eq9952
  have eq9956 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9953 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq9953
    | exact resolve eq9953 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9953
  have eq10224 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (k X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (k X0 X0)) (τ X0)
       have i₂ := eq9956 X0
       grind)
    | exact superpose eq9956 eq9
    | exact resolve eq9 eq9956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9956
  have eq25925 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1696 x y
       grind)
    | exact superpose eq1696 eq16
    | (have j1 := eq1696 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1696 x y
       grind)
    | exact resolve eq16 eq1696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq26117 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25925
  have eq26298 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8386 (σ x) (σ y)
       have i₂ := eq26117
       grind)
    | exact superpose eq26117 eq8386
    | exact resolve eq8386 eq26117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8386 eq26117
  have eq26304 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by grind
  clear eq26298
  have eq26310 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26304
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26304
    | exact resolve eq26304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26304
  have eq26408 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq206 x y
       have i₂ := eq26310
       grind)
    | exact superpose eq26310 eq206
    | exact resolve eq206 eq26310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26310
  have eq26470 : x = (M.op x x) := by grind
  clear eq26408
  have eq26588 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq120 x X0
       have i₂ := eq26470
       grind)
    | exact superpose eq26470 eq120
    | exact resolve eq120 eq26470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq26715 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq1521 x x x
       have i₂ := eq26470
       grind)
    | exact superpose eq26470 eq1521
    | exact resolve eq1521 eq26470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26470
  have eq26740 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq26715 X0
       have i₂ := eq206 x X0
       grind)
    | exact superpose eq206 eq26715
    | exact resolve eq26715 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq26715
  have eq28240 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26588 X0
       have i₂ := eq26740 X0
       grind)
    | exact superpose eq26740 eq26588
    | exact resolve eq26588 eq26740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26588
  have eq28243 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28240 y
       grind)
    | exact superpose eq28240 eq16
    | exact resolve eq16 eq28240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28244 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq26740 X0
       have i₂ := eq28240 X0
       grind)
    | exact superpose eq28240 eq26740
    | exact resolve eq26740 eq28240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26740
  have eq28376 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1521 x X1 X0
       have i₂ := eq28240 X0
       grind)
    | exact superpose eq28240 eq1521
    | exact resolve eq1521 eq28240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq28607 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28376 X0 X0
       have i₂ := eq28240 X0
       grind)
    | exact superpose eq28240 eq28376
    | exact resolve eq28376 eq28240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28240 eq28376
  have eq28973 : ∀ X0 : G, (k X0 (σ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq324 X0 x
       have i₂ := eq28244 (M.op (M.op x x) (τ (τ X0)))
       grind)
    | exact superpose eq28244 eq324
    | exact resolve eq324 eq28244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq28244
  have eq32674 : ∀ X0 : G, (M.op (M.op (M.op (τ (σ (σ x))) X0) (τ (σ (σ x)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10224 (σ (σ x)) X0
       have i₂ := eq28973 (σ (σ x))
       grind)
    | exact superpose eq28973 eq10224
    | exact resolve eq10224 eq28973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10224 eq28973
  have eq32759 : ∀ X0 : G, (M.op (τ (σ (σ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32674 X0
       have i₂ := eq28607 X0 (τ (σ (σ x)))
       grind)
    | exact superpose eq28607 eq32674
    | exact resolve eq32674 eq28607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28607 eq32674
  have eq32817 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32759 X0
       have i₂ := eq10 (σ x)
       grind)
    | exact superpose eq10 eq32759
    | exact resolve eq32759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32759
  have eq33399 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq28243
       have i₂ := eq32817 (σ y)
       grind)
    | exact superpose eq32817 eq28243
    | (have r₁ := eq28243
       have r₂ := eq32817 (σ y)
       grind)
    | exact resolve eq28243 eq32817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28243 eq32817
  have eq33580 : False := by grind
  exact eq33580

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq68 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (τ X0)) (M.op X1 X2))
       have i₂ := eq64 (τ X0) X1 X2
       grind)
    | exact superpose eq64 eq17
    | exact resolve eq17 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq69 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq107 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq9
    | exact resolve eq9 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq12
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq107 X0
       grind)
    | exact resolve eq12 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq61
    | exact resolve eq61 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq126 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op (M.op X0 X0) (τ X1)) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X1 (M.op X0 X0) X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq69
    | exact resolve eq69 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq130 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq121 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq132 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq130 (τ X0)
       grind)
    | exact superpose eq130 eq17
    | exact resolve eq17 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq133 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq132 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq132
    | exact resolve eq132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq206 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq120
    | exact resolve eq120 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq206 X0 X1
       grind)
    | exact superpose eq206 eq12
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq206 X0 X1
       grind)
    | exact resolve eq12 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq323 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op (M.op X1 X1) (τ (τ X0))) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op (M.op X1 X1) (τ (τ X0))) X1))
       have i₂ := eq126 X1 (τ X0)
       grind)
    | exact superpose eq126 eq17
    | exact resolve eq17 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq324 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op (M.op X1 X1) (τ (τ X0))) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq323
    | exact resolve eq323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq570 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq570
    | (have j0 := eq570 (σ X0) (σ X1)
       grind)
    | exact resolve eq570 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq570
    | (have j0 := eq570 (τ X0) (τ X1)
       grind)
    | exact resolve eq570 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq570 (τ X1) X0
       grind)
    | exact superpose eq570 eq17
    | (have j1 := eq570 (τ X1) X0
       grind)
    | exact resolve eq17 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1521 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq123
    | exact resolve eq123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1696 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X1 X0
       have i₂ := eq570 X1 X0
       grind)
    | exact superpose eq570 eq590
    | (have j0 := eq590 X1 X0
       have j1 := eq570 (σ X1) (σ X0)
       grind)
    | exact resolve eq590 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq2252 : ∀ X0 : G, (k X0 (k X0 (σ (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq618 (τ X0) X0
       grind)
    | exact superpose eq618 eq133
    | (have j1 := eq618 (τ X0) X0
       grind)
    | exact resolve eq133 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq618
  have eq2272 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2252 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2252
    | (have j0 := eq2252 X0
       grind)
    | exact resolve eq2252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252
  have eq2789 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) X1)))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (τ X0) X1
       have i₂ := eq2272 X0
       grind)
    | exact superpose eq2272 eq69
    | (have j1 := eq2272 X0
       grind)
    | exact resolve eq69 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq2793 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ X0)) X1) = X1 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq120 (τ X0) X1
       have i₂ := eq2272 X0
       grind)
    | exact superpose eq2272 eq120
    | (have j1 := eq2272 X0
       grind)
    | exact resolve eq120 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2838 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) (M.op (τ X0) X1)) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1521 (τ X0) (τ X0) x
       have i₂ := eq2272 X0
       grind)
    | exact superpose eq2272 eq1521
    | (have j1 := eq2272 X0
       grind)
    | exact resolve eq1521 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq2846 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2838 X0 X1
       have i₂ := eq206 (τ X0) X1
       grind)
    | exact superpose eq206 eq2838
    | (have j0 := eq2838 X0 X1
       grind)
    | exact resolve eq2838 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2838
  have eq2863 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2789 X0 X1
       have i₂ := eq206 (τ X0) X1
       grind)
    | exact superpose eq206 eq2789
    | (have j0 := eq2789 X0 X1
       grind)
    | exact resolve eq2789 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789
  have eq3432 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) ∨ (σ X0) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ (M.op (τ (σ X0)) X1))
       have i₂ := eq2863 (σ X0) X1
       grind)
    | exact superpose eq2863 eq28
    | (have j1 := eq2863 (σ X0) X1
       grind)
    | exact resolve eq28 eq2863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq3448 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) X1)) ∨ (σ X0) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3432 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq3432
    | (have j0 := eq3432 X0 X1
       grind)
    | exact resolve eq3432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432
  have eq3459 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (σ X0) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3448 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3448
    | (have j0 := eq3448 X0 X1
       grind)
    | exact resolve eq3448 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3448
  have eq3468 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3459 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3459
    | (have j0 := eq3459 X0 X1
       grind)
    | exact resolve eq3459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3459
  have eq3472 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3468 X0 X1
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq3468
    | (have j0 := eq3468 X0 X1
       grind)
    | exact resolve eq3468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq3759 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (k X0 X0)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq3472 X0 X1
       grind)
    | exact superpose eq3472 eq10
    | (have j1 := eq3472 X0 X1
       grind)
    | exact resolve eq10 eq3472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472
  have eq3789 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3759 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3759
    | (have j0 := eq3759 X0 X1
       grind)
    | exact resolve eq3759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3759
  have eq8290 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq592 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq8386 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8290 X0 (M.op X0 X1)
       have i₂ := eq245 X0 X1
       grind)
    | exact superpose eq245 eq8290
    | (have j0 := eq8290 X0 (M.op X0 X1)
       grind)
    | exact resolve eq8290 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq8290
  have eq9420 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq2846 eq2793
    | (have j0 := eq2793 X0 X1
       have j1 := eq2846 X0 X1
       grind)
    | exact resolve eq2793 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793 eq2846
  have eq9439 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (M.op (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (k (σ X0) (σ X0))
       have i₂ := eq9420 (σ X0) X1
       grind)
    | exact superpose eq9420 eq28
    | (have j1 := eq9420 (σ X0) X1
       grind)
    | exact resolve eq28 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9420
  have eq9458 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (k (τ (σ X0)) X0)) ∨ (M.op (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9439 X0 X1
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq9439
    | (have j0 := eq9439 X0 X1
       grind)
    | exact resolve eq9439 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9439
  have eq9472 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9458 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9458
    | (have j0 := eq9458 X0 X1
       grind)
    | exact resolve eq9458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9458
  have eq9478 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9472 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9472
    | (have j0 := eq9472 X0 X1
       grind)
    | exact resolve eq9472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9472
  have eq9479 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq9478 eq3789
    | (have j0 := eq3789 X0 X1
       have j1 := eq9478 X0 X1
       grind)
    | exact resolve eq3789 eq9478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789 eq9478
  have eq9559 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq9479 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9479
  have eq9560 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq9559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9559
  have eq9596 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9560 X0
       have i₂ := eq570 X0 (k X0 X0)
       grind)
    | exact superpose eq570 eq9560
    | (have j1 := eq570 X0 (k X0 X0)
       grind)
    | exact resolve eq9560 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq9560
  have eq9652 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op (k X0 X0) X1)) X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (k X0 X0) X1
       have i₂ := eq9596 X0
       grind)
    | exact superpose eq9596 eq9
    | (have j1 := eq9596 X0
       grind)
    | exact resolve eq9 eq9596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9738 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9596 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9780 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9652 X0 X1
       have i₂ := eq206 (k X0 X0) X1
       grind)
    | exact superpose eq206 eq9652
    | (have j0 := eq9652 X0 X1
       grind)
    | exact resolve eq9652 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9652
  have eq10246 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9780 X0 X0
       have i₂ := eq9596 X0
       grind)
    | exact superpose eq9596 eq9780
    | (have j0 := eq9780 X0 x
       have j1 := eq9596 X0
       grind)
    | exact resolve eq9780 eq9596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9596 eq9780
  have eq10398 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10246 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10246
  have eq10449 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10398 X0
       have j1 := eq9738 X0
       grind)
    | (have r₁ := eq10398 X0
       have r₂ := eq9738 X0
       grind)
    | exact resolve eq10398 eq9738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9738 eq10398
  have eq10518 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10449 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq10449
    | exact resolve eq10449 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq10449
  have eq10790 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (k X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (k X0 X0)) (τ X0)
       have i₂ := eq10518 X0
       grind)
    | exact superpose eq10518 eq9
    | exact resolve eq9 eq10518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10518
  have eq26288 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1696 x y
       grind)
    | exact superpose eq1696 eq16
    | (have j1 := eq1696 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1696 x y
       grind)
    | exact resolve eq16 eq1696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq26480 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26288
  have eq26661 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8386 (σ x) (σ y)
       have i₂ := eq26480
       grind)
    | exact superpose eq26480 eq8386
    | exact resolve eq8386 eq26480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8386 eq26480
  have eq26667 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by grind
  clear eq26661
  have eq26673 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26667
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26667
    | exact resolve eq26667 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26667
  have eq26771 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq206 x y
       have i₂ := eq26673
       grind)
    | exact superpose eq26673 eq206
    | exact resolve eq206 eq26673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26673
  have eq26833 : x = (M.op x x) := by grind
  clear eq26771
  have eq26951 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq120 x X0
       have i₂ := eq26833
       grind)
    | exact superpose eq26833 eq120
    | exact resolve eq120 eq26833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq27078 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq1521 x x x
       have i₂ := eq26833
       grind)
    | exact superpose eq26833 eq1521
    | exact resolve eq1521 eq26833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26833
  have eq27103 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq27078 X0
       have i₂ := eq206 x X0
       grind)
    | exact superpose eq206 eq27078
    | exact resolve eq27078 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq27078
  have eq28243 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26951 X0
       have i₂ := eq27103 X0
       grind)
    | exact superpose eq27103 eq26951
    | exact resolve eq26951 eq27103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26951
  have eq28246 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28243 y
       grind)
    | exact superpose eq28243 eq16
    | exact resolve eq16 eq28243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28247 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq27103 X0
       have i₂ := eq28243 X0
       grind)
    | exact superpose eq28243 eq27103
    | exact resolve eq27103 eq28243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27103
  have eq28379 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1521 x X1 X0
       have i₂ := eq28243 X0
       grind)
    | exact superpose eq28243 eq1521
    | exact resolve eq1521 eq28243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq28610 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28379 X0 X0
       have i₂ := eq28243 X0
       grind)
    | exact superpose eq28243 eq28379
    | exact resolve eq28379 eq28243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28243 eq28379
  have eq28976 : ∀ X0 : G, (k X0 (σ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq324 X0 x
       have i₂ := eq28247 (M.op (M.op x x) (τ (τ X0)))
       grind)
    | exact superpose eq28247 eq324
    | exact resolve eq324 eq28247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq28247
  have eq31304 : ∀ X0 : G, (M.op (M.op (M.op (τ (σ (σ x))) X0) (τ (σ (σ x)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10790 (σ (σ x)) X0
       have i₂ := eq28976 (σ (σ x))
       grind)
    | exact superpose eq28976 eq10790
    | exact resolve eq10790 eq28976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10790 eq28976
  have eq31383 : ∀ X0 : G, (M.op (τ (σ (σ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31304 X0
       have i₂ := eq28610 X0 (τ (σ (σ x)))
       grind)
    | exact superpose eq28610 eq31304
    | exact resolve eq31304 eq28610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28610 eq31304
  have eq31439 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31383 X0
       have i₂ := eq10 (σ x)
       grind)
    | exact superpose eq10 eq31383
    | exact resolve eq31383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31383
  have eq31461 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq28246
       have i₂ := eq31439 (σ y)
       grind)
    | exact superpose eq31439 eq28246
    | (have r₁ := eq28246
       have r₂ := eq31439 (σ y)
       grind)
    | exact resolve eq28246 eq31439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28246 eq31439
  have eq31640 : False := by grind
  exact eq31640

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq164 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq86 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq86
    | exact resolve eq86 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 y
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq208 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op x X0) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq178 eq13
    | (have r₁ := eq13 X0 (M.op (M.op x X0) (M.op x y))
       have r₂ := eq178 X0
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq211 : ∀ X0 : G, (k X0 (M.op (M.op x X0) (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq208 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq224 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x (M.op x y)) (M.op x y)))) := by
    first
    | exact superpose eq211 eq38
    | exact resolve eq38 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq211
  have eq225 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x (M.op x y)) (M.op x y)))) := by
    first
    | exact superpose eq20 eq224
    | exact resolve eq224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq580 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
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
  have eq581 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq629 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq580
       grind)
    | exact superpose eq580 eq40
    | exact resolve eq40 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq580
  have eq633 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq632
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq632
    | exact resolve eq632 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq635 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq633
    | exact resolve eq633 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq635 eq581
    | exact resolve eq581 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq643
       have r₂ := eq27
       grind)
    | exact resolve eq643 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq654 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq650 eq27
    | exact resolve eq27 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq650 eq176
    | exact resolve eq176 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq657 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq650 eq182
    | exact resolve eq182 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq686 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq655 eq16
    | exact resolve eq16 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq1343 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq650 eq629
    | (have r₁ := eq629
       have r₂ := eq650
       grind)
    | exact resolve eq629 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq1344 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1343
  have eq1347 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1344 eq635
    | exact resolve eq635 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq1353 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1347
  have eq1380 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1353 eq635
    | exact resolve eq635 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq1382 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1353 eq657
    | (have r₁ := eq657
       have r₂ := eq1353
       grind)
    | exact resolve eq657 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq1353
  have eq1451 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1382
  have eq1452 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1451
  have eq1454 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1380
  have eq1459 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1452 eq1454
    | exact resolve eq1454 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq1454
  have eq1477 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1459
       have r₂ := eq654
       grind)
    | exact resolve eq1459 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq1490 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1477 eq654
    | exact resolve eq654 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq1477
  have eq1507 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq1490
  have eq1573 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq3668 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f3668_13 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
      intro X0 X1 X2 X3
      grind
    have f3668_14 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ x = (M.op x y) := by
      intro X0 X1
      grind
    have f3668_23 : (σ y) ≠ (M.op (M.op (σ x) X0) (σ y)) := by grind
    have f3668_24 : x ≠ (M.op x y) := by grind
    have f3668_26 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 := by
      intro X0 X1
      first
      | (have j0 := f3668_14 X0 X1
         grind)
      | (have r₁ := f3668_14 X0 X1
         have r₂ := f3668_24
         grind)
      | exact resolve f3668_14 f3668_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3668_94 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) := by
      intro X0
      first
      | (have i₁ := f3668_13 (M.op (σ x) X0) (σ x) X0 (σ y)
         have i₂ := f3668_26 X0 (M.op (σ x) X0)
         grind)
      | exact superpose f3668_26 f3668_13
      | exact resolve f3668_13 f3668_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3668_101 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f3668_23
         have i₂ := f3668_94 X0
         grind)
      | exact superpose f3668_94 f3668_23
      | (have r₁ := f3668_23
         have r₂ := f3668_94 X0
         grind)
      | exact resolve f3668_23 f3668_94
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3668_109 : False := by grind
    exact f3668_109
  clear eq180 eq686
  have eq3692 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3668
    | (have j0 := eq3668 (σ y)
       grind)
    | exact resolve eq3668 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668
  have eq3732 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq650 eq3692
    | exact resolve eq3692 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3692
  have eq3733 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3732
    | exact resolve eq3732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3732
  have eq3734 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq650 eq3733
    | exact resolve eq3733 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq3733
  have eq3735 : x = (M.op x y) := by
    first
    | (have r₁ := eq3734
       have r₂ := eq1507
       grind)
    | exact resolve eq3734 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507 eq3734
  have eq3736 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3735
       grind)
    | exact superpose eq3735 eq18
    | exact resolve eq18 eq3735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3737 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq3735
       grind)
    | exact superpose eq3735 eq22
    | exact resolve eq22 eq3735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3745 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)))) := by
    first
    | (have i₁ := eq225
       have i₂ := eq3735
       grind)
    | exact superpose eq3735 eq225
    | exact resolve eq225 eq3735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3748 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3745
       have i₂ := eq1573 sF0
       grind)
    | exact superpose eq1573 eq3745
    | exact resolve eq3745 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3745
  have eq3749 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3748
    | exact resolve eq3748 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748
  have eq3751 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3737 eq20
    | exact resolve eq20 eq3737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3788 : (σ x) = (k (σ x) (σ (M.op (M.op x (M.op x y)) (M.op x y)))) := by
    first
    | exact superpose eq3751 eq225
    | exact resolve eq225 eq3751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq3801 : (σ x) = (k (σ x) (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)))) := by
    first
    | (have i₁ := eq3788
       have i₂ := eq3735
       grind)
    | exact superpose eq3735 eq3788
    | exact resolve eq3788 eq3735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3735 eq3788
  have eq3809 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3801
       have i₂ := eq1573 sF0
       grind)
    | exact superpose eq1573 eq3801
    | exact resolve eq3801 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573 eq3801
  have eq3817 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3809
    | exact resolve eq3809 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3809
  have eq3818 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3751 eq3817
    | exact resolve eq3817 eq3751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817
  have eq3888 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq3749 eq164
    | exact resolve eq164 eq3749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq3749
  have eq3896 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq3888
    | exact resolve eq3888 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3888
  have eq3958 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3896 eq620
    | (have j0 := eq620 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq620 (M.op x y) (M.op x y)
       have r₂ := eq3896
       grind)
    | exact resolve eq620 eq3896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq3896
  have eq3959 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq3958
  have eq3985 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq3959 eq185
    | exact resolve eq185 eq3959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq3959
  have eq4001 : y = (M.op x y) := by
    first
    | exact superpose eq3736 eq3985
    | exact resolve eq3985 eq3736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736 eq3985
  have eq4005 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4001
       grind)
    | exact superpose eq4001 eq24
    | exact resolve eq24 eq4001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4001
  have eq4043 : (σ x) = (σ y) := by
    first
    | exact superpose eq3737 eq4005
    | exact resolve eq4005 eq3737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3737 eq4005
  have eq4062 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4043 eq581
    | exact resolve eq581 eq4043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq4043
  have eq4120 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3818 eq4062
    | exact resolve eq4062 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3818 eq4062
  have eq4121 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4120
  have eq4153 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4121 eq27
    | exact resolve eq27 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4121
  have eq4170 : False := by grind
  exact eq4170

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq570 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq570
    | (have j0 := eq570 (σ X0) (σ X1)
       grind)
    | exact resolve eq570 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq570
    | (have j0 := eq570 (τ X0) (τ X1)
       grind)
    | exact resolve eq570 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1641 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X1 X0
       have i₂ := eq570 X1 X0
       grind)
    | exact superpose eq570 eq590
    | (have j0 := eq590 X1 X0
       have j1 := eq570 (σ X1) (σ X0)
       grind)
    | exact resolve eq590 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq8188 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq592 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq8285 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8188 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8188
    | (have j0 := eq8188 (σ X1) (σ X0)
       grind)
    | exact resolve eq8188 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8188
  have eq8307 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8285 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8285
    | (have j0 := eq8285 X0 X1
       grind)
    | exact resolve eq8285 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8285
  have eq8334 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8307 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq8307
    | (have j0 := eq8307 X0 X1
       grind)
    | exact resolve eq8307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8307
  have eq8358 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8334 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8334
    | (have j0 := eq8334 X0 X1
       grind)
    | exact resolve eq8334 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8334
  have eq8373 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8358 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8358
    | (have j0 := eq8358 X0 X1
       grind)
    | exact resolve eq8358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8358
  have eq8445 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8373 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8373
    | (have j0 := eq8373 (σ X0) (σ X1)
       grind)
    | exact resolve eq8373 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8373
  have eq24962 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1641 x y
       grind)
    | exact superpose eq1641 eq16
    | (have j1 := eq1641 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1641 x y
       grind)
    | exact resolve eq16 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq25150 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24962
  have eq25222 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25150
       grind)
    | exact superpose eq25150 eq16
    | exact resolve eq16 eq25150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25231 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq25150
       grind)
    | exact superpose eq25150 eq12
    | exact resolve eq12 eq25150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25232 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq25150
       grind)
    | exact superpose eq25150 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25150
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25150
       grind)
    | exact resolve eq13 eq25150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25150
  have eq25333 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq25232
  have eq25375 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25333
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq25333
    | exact resolve eq25333 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25333
  have eq25376 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25231
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq25231
    | exact resolve eq25231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25231
  have eq25385 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq570 eq25375
    | (have j1 := eq570 y x
       grind)
    | exact resolve eq25375 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25375
  have eq25386 : (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq570 eq25376
    | (have j1 := eq570 y x
       grind)
    | exact resolve eq25376 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq25376
  have eq25389 : x = (M.op x y) := by grind
  clear eq25222 eq25385 eq25386
  have eq25392 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25389
       grind)
    | exact superpose eq25389 eq16
    | exact resolve eq16 eq25389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25395 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq25389
       grind)
    | exact superpose eq25389 eq12
    | exact resolve eq12 eq25389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25396 : x ≠ x ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq25389
       grind)
    | exact superpose eq25389 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25389
       grind)
    | exact resolve eq13 eq25389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25389
  have eq25497 : x = y ∨ x = (k y x) := by grind
  clear eq25396
  have eq25536 : x = (k y x) := by
    first
    | (have r₁ := eq25395
       have r₂ := eq25497
       grind)
    | exact resolve eq25395 eq25497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25395 eq25497
  have eq25855 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8445 y x
       have i₂ := eq25536
       grind)
    | exact superpose eq25536 eq8445
    | (have j0 := eq8445 y x
       grind)
    | exact resolve eq8445 eq25536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8445 eq25536
  have eq25856 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25855
  have eq25862 : False := by grind
  exact eq25862

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq18
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq121 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq9
    | exact resolve eq9 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq207 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq121
    | exact resolve eq121 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq234 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq207 X0 X1
       grind)
    | exact superpose eq207 eq12
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq207 X0 X1
       grind)
    | exact resolve eq12 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq234 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq255 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) X1) X0
       have i₂ := eq246 (σ X0) X1
       grind)
    | exact superpose eq246 eq23
    | exact resolve eq23 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq513 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq14 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq513 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq513
    | (have j0 := eq513 (σ X0) (σ X1)
       grind)
    | exact resolve eq513 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2228 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq531 X1 X0
       have i₂ := eq513 X1 X0
       grind)
    | exact superpose eq513 eq531
    | (have j0 := eq531 X1 X0
       have j1 := eq513 (σ X1) (σ X0)
       grind)
    | exact resolve eq531 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27403 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2228 x y
       grind)
    | exact superpose eq2228 eq16
    | (have j1 := eq2228 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2228 x y
       grind)
    | exact resolve eq16 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq27616 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq27403
  have eq27695 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq255 x (σ x)
       have i₂ := eq27616
       grind)
    | exact superpose eq27616 eq255
    | exact resolve eq255 eq27616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq27810 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq207 (σ x) (σ x)
       have i₂ := eq27616
       grind)
    | exact superpose eq27616 eq207
    | exact resolve eq207 eq27616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27616
  have eq27890 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq27695
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq27695
    | exact resolve eq27695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27695
  have eq28431 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq513 y x
       have i₂ := eq27890
       grind)
    | exact superpose eq27890 eq513
    | (have j0 := eq513 y x
       grind)
    | exact resolve eq513 eq27890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq27890
  have eq28432 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq28431
  have eq31778 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27810
       grind)
    | exact superpose eq27810 eq16
    | exact resolve eq16 eq27810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27810
  have eq31923 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28432 eq31778
    | exact resolve eq31778 eq28432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28432 eq31778
  have eq31924 : y = (M.op x x) := by grind
  clear eq31923
  have eq32040 : y = (M.op x y) := by
    first
    | (have i₁ := eq207 x x
       have i₂ := eq31924
       grind)
    | exact superpose eq31924 eq207
    | exact resolve eq207 eq31924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32041 : y = (k y x) := by
    first
    | (have i₁ := eq246 x x
       have i₂ := eq31924
       grind)
    | exact superpose eq31924 eq246
    | exact resolve eq246 eq31924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq31924
  have eq32127 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32040
       grind)
    | exact superpose eq32040 eq16
    | exact resolve eq16 eq32040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32040
  have eq32259 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq531 y x
       have i₂ := eq32041
       grind)
    | exact superpose eq32041 eq531
    | (have j0 := eq531 y x
       grind)
    | exact resolve eq531 eq32041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq32041
  have eq32261 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq32259
       have r₂ := eq32127
       grind)
    | exact resolve eq32259 eq32127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32259
  have eq32388 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq207 (σ x) (σ x)
       have i₂ := eq32261
       grind)
    | exact superpose eq32261 eq207
    | exact resolve eq207 eq32261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq32261
  have eq32463 : False := by grind
  exact eq32463

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq14 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44
    | (have j0 := eq44 (σ X0) (σ X1)
       grind)
    | exact resolve eq44 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq78 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq78 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq105 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 (τ X0)) (M.op X1 X2))
       have i₂ := eq35 (τ X0) X1 X2
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35
  have eq106 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq105
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq135 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq170 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq200 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op (M.op X0 X0) (τ X1)) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1 (M.op X0 X0) X0
       have i₂ := eq135 X0
       grind)
    | exact superpose eq135 eq106
    | exact resolve eq106 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq135
  have eq211 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 y x
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq245 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (M.op (M.op X1 X1) (τ (σ X0))) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ (M.op (M.op (M.op X1 X1) (τ (σ X0))) X1))
       have i₂ := eq200 X1 (σ X0)
       grind)
    | exact superpose eq200 eq31
    | exact resolve eq31 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq200
  have eq248 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op (M.op (M.op X1 X1) (τ (σ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq245 X0 X1
       have i₂ := eq10 (M.op (M.op (M.op X1 X1) (τ (σ X0))) X1)
       grind)
    | exact superpose eq10 eq245
    | exact resolve eq245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq252 : ∀ X0 X1 : G, (k X0 (M.op (M.op (M.op X1 X1) X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq248
    | exact resolve eq248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq485 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq252 (M.op X0 X1) X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq252
    | exact resolve eq252 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq599 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) X1) X0
       have i₂ := eq485 (σ X0) X1
       grind)
    | exact superpose eq485 eq23
    | exact resolve eq23 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq485
  have eq603 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq211
       have i₂ := eq44 y x
       grind)
    | exact superpose eq44 eq211
    | (have j1 := eq44 (σ y) (σ x)
       grind)
    | exact resolve eq211 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq603
  have eq1061 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79 x
       have i₂ := eq604
       grind)
    | exact superpose eq604 eq79
    | exact resolve eq79 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1414 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq211
       have i₂ := eq1061
       grind)
    | exact superpose eq1061 eq211
    | exact resolve eq211 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq1061
  have eq1416 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1414
  have eq1600 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq170 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq170
    | exact resolve eq170 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq1638 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1600 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1600
    | exact resolve eq1600 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq6915 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1638 x x
       have i₂ := eq604
       grind)
    | exact superpose eq604 eq1638
    | exact resolve eq1638 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq8069 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1416
       have i₂ := eq6915
       grind)
    | exact superpose eq6915 eq1416
    | exact resolve eq1416 eq6915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416 eq6915
  have eq8070 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq8069
  have eq8071 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq8070
  have eq8085 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | (have i₁ := eq599 x (σ x)
       have i₂ := eq8071
       grind)
    | exact superpose eq8071 eq599
    | exact resolve eq599 eq8071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq8160 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1638 (σ x) (σ x)
       have i₂ := eq8071
       grind)
    | exact superpose eq8071 eq1638
    | exact resolve eq1638 eq8071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8071
  have eq8175 : y = (k y x) := by
    first
    | (have i₁ := eq8085
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8085
    | exact resolve eq8085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8085
  have eq8181 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8175
       have i₂ := eq44 y x
       grind)
    | exact superpose eq44 eq8175
    | (have j1 := eq44 y x
       grind)
    | exact resolve eq8175 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq8175
  have eq9131 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8160
       grind)
    | exact superpose eq8160 eq16
    | exact resolve eq16 eq8160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8160
  have eq9276 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9131
       have i₂ := eq8181
       grind)
    | exact superpose eq8181 eq9131
    | exact resolve eq9131 eq8181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8181
  have eq9347 : y = (M.op x x) := by grind
  clear eq9276
  have eq9794 : y = (M.op x y) := by
    first
    | (have i₁ := eq1638 x x
       have i₂ := eq9347
       grind)
    | exact superpose eq9347 eq1638
    | exact resolve eq1638 eq9347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638 eq9347
  have eq10144 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq9131
       have i₂ := eq9794
       grind)
    | exact superpose eq9794 eq9131
    | exact resolve eq9131 eq9794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9131 eq9794
  have eq10215 : False := by grind
  exact eq10215

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq9
    | exact resolve eq9 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq12
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq107 X0
       grind)
    | exact resolve eq12 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq61
    | exact resolve eq61 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq107
  have eq130 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq121 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq206 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq120
    | exact resolve eq120 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq206 X0 X1
       grind)
    | exact superpose eq206 eq12
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq206 X0 X1
       grind)
    | exact resolve eq12 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq254 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) X1) X0
       have i₂ := eq245 (σ X0) X1
       grind)
    | exact superpose eq245 eq22
    | exact resolve eq22 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq245
  have eq570 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq570
    | (have j0 := eq570 X0 (σ X1)
       grind)
    | exact resolve eq570 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq570 (τ (M.op (σ X0) X1)) X0
       have i₂ := eq254 X0 X1
       grind)
    | exact superpose eq254 eq570
    | (have j0 := eq570 X0 X0
       grind)
    | exact resolve eq570 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq631 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 X1) X0 X2 X3
       have i₂ := eq206 X0 X1
       grind)
    | exact superpose eq206 eq62
    | exact resolve eq62 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1572 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq123
    | exact resolve eq123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1648 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X1 X0
       have i₂ := eq570 X1 X0
       grind)
    | exact superpose eq570 eq590
    | (have j0 := eq590 X0 X0
       have j1 := eq570 X0 (σ X0)
       grind)
    | exact resolve eq590 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq18999 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1648 x y
       grind)
    | exact superpose eq1648 eq16
    | (have j1 := eq1648 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1648 x y
       grind)
    | exact resolve eq16 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq19208 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq18999
  have eq19258 : (τ (σ x)) = (M.op x (τ (σ x))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq593 x (σ x)
       have i₂ := eq19208
       grind)
    | exact superpose eq19208 eq593
    | (have j0 := eq593 x x
       grind)
    | exact resolve eq593 eq19208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq19208
  have eq19436 : (τ (σ x)) = (M.op x (τ (σ x))) ∨ x = (M.op x x) := by grind
  clear eq19258
  have eq19496 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq19436
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19436
    | exact resolve eq19436 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19436
  have eq19497 : x = (M.op x x) := by grind
  clear eq19496
  have eq19516 : x = (M.op x x) := by grind
  clear eq19497
  have eq19522 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq120 x X0
       have i₂ := eq19516
       grind)
    | exact superpose eq19516 eq120
    | exact resolve eq120 eq19516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq19529 : x = (k x x) := by
    first
    | (have i₁ := eq130 x
       have i₂ := eq19516
       grind)
    | exact superpose eq19516 eq130
    | exact resolve eq130 eq19516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq19660 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq1572 x x x
       have i₂ := eq19516
       grind)
    | exact superpose eq19516 eq1572
    | exact resolve eq1572 eq19516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19516
  have eq19694 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq19660 X0
       have i₂ := eq206 x X0
       grind)
    | exact superpose eq206 eq19660
    | exact resolve eq19660 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq19660
  have eq19751 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq590 x x
       have i₂ := eq19529
       grind)
    | exact superpose eq19529 eq590
    | (have j0 := eq590 x x
       grind)
    | exact resolve eq590 eq19529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq19529
  have eq19754 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq19751
  have eq20489 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19522 X0
       have i₂ := eq19694 X0
       grind)
    | exact superpose eq19694 eq19522
    | exact resolve eq19522 eq19694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19522 eq19694
  have eq20490 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20489 y
       grind)
    | exact superpose eq20489 eq16
    | exact resolve eq16 eq20489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20604 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op x X1) X0) X2) (M.op x X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq631 x X1 X0 X2
       have i₂ := eq20489 X0
       grind)
    | exact superpose eq20489 eq631
    | exact resolve eq631 eq20489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq20635 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1572 x X1 X0
       have i₂ := eq20489 X0
       grind)
    | exact superpose eq20489 eq1572
    | exact resolve eq1572 eq20489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq20863 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20635 X0 X0
       have i₂ := eq20489 X0
       grind)
    | exact superpose eq20489 eq20635
    | exact resolve eq20635 eq20489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20635
  have eq20887 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20604 X0 X0 X2
       have i₂ := eq20489 X0
       grind)
    | exact superpose eq20489 eq20604
    | exact resolve eq20604 eq20489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20489 eq20604
  have eq29029 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20887 (σ x) (σ x) X0
       have i₂ := eq19754
       grind)
    | exact superpose eq19754 eq20887
    | exact resolve eq20887 eq19754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19754 eq20887
  have eq29225 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29029 X0
       have i₂ := eq20863 X0 (σ x)
       grind)
    | exact superpose eq20863 eq29029
    | exact resolve eq29029 eq20863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20863 eq29029
  have eq29826 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq20490
       have i₂ := eq29225 (σ y)
       grind)
    | exact superpose eq29225 eq20490
    | (have r₁ := eq20490
       have r₂ := eq29225 (σ y)
       grind)
    | exact resolve eq20490 eq29225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20490 eq29225
  have eq29961 : False := by grind
  exact eq29961

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_x_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq131 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq22 eq37
  have eq442 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq450 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq442 X0
       grind)
    | exact superpose eq442 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq442 X0
       grind)
    | exact resolve eq13 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq442 X0
       grind)
    | exact superpose eq442 eq14
    | exact resolve eq14 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq457 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq450 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq604 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq95 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq606 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq604 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq1367 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59 eq452
    | exact resolve eq452 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1370 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq452
    | exact resolve eq452 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq1408 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq1367 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1367
       grind)
    | exact resolve eq13 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq1408
  have eq1440 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1419 eq131
    | exact resolve eq131 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq1419
  have eq1444 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq1440
    | exact resolve eq1440 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq1466 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1444 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444
  have eq1467 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1466
  have eq1685 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1467 eq57
    | exact resolve eq57 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1686 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1467 eq60
    | exact resolve eq60 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1467
  have eq1724 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1370 eq1686
    | exact resolve eq1686 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370 eq1686
  have eq5397 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq606 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq606
    | (have j0 := eq606 (τ X0)
       grind)
    | exact resolve eq606 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq606
  have eq5407 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5397 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5397
    | (have j0 := eq5397 X0
       grind)
    | exact resolve eq5397 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5397
  have eq5413 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5407 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5407
    | (have j0 := eq5407 X0
       grind)
    | exact resolve eq5407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5407
  have eq13489 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1724 eq1685
    | exact resolve eq1685 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685 eq1724
  have eq13541 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq13489
  have eq13542 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13541
    | exact resolve eq13541 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13541
  have eq24780 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq24790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq24780
    | exact resolve eq24780 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24780
  have eq24801 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24790
       have r₂ := eq27
       grind)
    | exact resolve eq24790 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24790
  have eq24804 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq24801
    | exact resolve eq24801 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24801
  have eq24840 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24804 eq457
    | exact resolve eq457 eq24804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq24804
  have eq24937 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24840 eq49
    | exact resolve eq49 eq24840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq24840
  have eq24995 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq24937
    | exact resolve eq24937 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24937
  have eq25000 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq5413 x
       grind)
    | (have r₁ := eq24995
       have r₂ := eq5413 x
       grind)
    | exact resolve eq24995 eq5413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5413 eq24995
  have eq25023 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq70 X0 x
       have i₂ := eq25000
       grind)
    | exact superpose eq25000 eq70
    | (have j0 := eq70 X0 x
       grind)
    | (have r₁ := eq70 X0 x
       have r₂ := eq25000
       grind)
    | exact resolve eq70 eq25000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq25000
  have eq25081 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq25023 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25023
  have eq25374 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq25081 y
       grind)
    | exact superpose eq25081 eq76
    | exact resolve eq76 eq25081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq25081
  have eq25445 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25374
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25374
    | exact resolve eq25374 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25374
  have eq25479 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq25445
       have r₂ := eq51
       grind)
    | exact resolve eq25445 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq25445
  have eq25496 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25479 eq83
    | exact resolve eq83 eq25479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq25479
  have eq25526 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq25496
    | exact resolve eq25496 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25496
  have eq25530 : y = (k y x) := by
    first
    | (have r₁ := eq25526
       have r₂ := eq50
       grind)
    | exact resolve eq25526 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq25526
  have eq25539 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq25530
       grind)
    | exact superpose eq25530 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq25530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25530
  have eq25550 : y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq25539
  have eq25561 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25550
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25550
    | exact resolve eq25550 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25550
  have eq25780 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq25561
       grind)
    | exact superpose eq25561 eq56
    | exact resolve eq56 eq25561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq25781 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq25561
       grind)
    | exact superpose eq25561 eq59
    | exact resolve eq59 eq25561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq25561
  have eq25894 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1367 eq25781
    | exact resolve eq25781 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367 eq25781
  have eq30524 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25894 eq25780
    | exact resolve eq25780 eq25894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25780 eq25894
  have eq30577 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq30524
  have eq30578 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30577
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30577
    | exact resolve eq30577 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq30577
  have eq30579 : y = (M.op x y) := by grind
  clear eq30578
  have eq30749 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq30579 eq20
    | exact resolve eq20 eq30579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30579
  have eq30903 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq30749
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30749
    | exact resolve eq30749 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq30749
  have eq30910 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30903 eq26
    | exact resolve eq26 eq30903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30910 eq13542
    | exact resolve eq13542 eq30910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13542 eq30910
  have eq31484 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31392
       have r₂ := eq27
       grind)
    | exact resolve eq31392 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31392
  have eq31490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30903 eq31484
    | exact resolve eq31484 eq30903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30903 eq31484
  have eq31492 : False := by grind
  exact eq31492
